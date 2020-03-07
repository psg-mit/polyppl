"""Simplifcation Transformation."""

from typing import Callable, List, Dict, Set, Optional, Tuple

import abc
import enum
import copy
import ast
from collections import defaultdict

import ast_scope
import astor
import islpy

from polyppl.isl_utils import aff_align_in_ids, basic_set_zero
import polyppl.ir as ir
import polyppl.schedule as schedule
import polyppl.code_gen as code_gen
import polyppl.isl_utils as isl_utils


def _make_subscript_ast(lhs_name: ir.VarID,
                        rhs_asts: List[ast.AST],
                        store=True):
  if len(rhs_asts) == 1:
    rhs = rhs_asts[0]
  else:
    rhs = ast.Tuple(elts=rhs_asts)
  return ast.Subscript(value=ast.Name(id=lhs_name,
                                      ctx=ast.Store() if store else ast.Load()),
                       slice=ast.Index(value=rhs))


def _make_simple_subscript_ast(lhs_name: ir.VarID,
                               rhs_names: List[ir.VarID],
                               store=True):
  rhs_asts = [ast.Name(id=name, ctx=ast.Load()) for name in rhs_names]
  return _make_subscript_ast(lhs_name, rhs_asts, store=store)


def simplification_transformation(prog: ir.Program,
                                  stmt_id: ir.Program.StatementID,
                                  r_e: islpy.MultiVal) -> ir.Program:
  """Apply Simplification Transformation with given constant reuse direction."""
  r_e = islpy.MultiAff.multi_val_on_space(r_e.get_space(), r_e)
  r_e = r_e.add(r_e.identity_multi_aff())
  r_e = r_e.align_params(
      prog.get_statement_by_id(stmt_id).domain.get_space().params())
  return simplification_transformation_core(prog, stmt_id, r_e)


def simplification_transformation_core(
    prog: ir.Program,
    stmt_id: ir.Program.StatementID,
    r_e: islpy.MultiAff,
    r_e_symb_domain: islpy.Set = None) -> ir.Program:
  """Apply Simplification Transformation with given reuse direction.

  We allow the reuse direction to be symbolic.

  Args:
    prog: the input program.

    stmt_id: the stmt_id in the program to be applied ST with.

    r_e: the reuse direction, as a MultiAff. Note that r_e can be symbolic. For
    example, [N, u, v] -> { [i, j] -> [i+u, j+v] } is a valid symbolic reuse
    direction. In this example, u and v are deduced to be the symbolic
    parameters, because prog.param_space_names == ['N'].

    r_e_symb_domain: if r_e is symbolic, then r_e_symb_domain is the constraint
    put on the symbolic parameters. In the above example, a valid
    r_e_symb_domain could be [N, u, v] -> { : u < 0 or u > 0 }.

  Returns:
    the transformed program.
  """

  is_symbolic_st = r_e_symb_domain is not None
  if is_symbolic_st:
    if not r_e.get_space().params() == r_e_symb_domain.get_space():
      raise ValueError("Invalid symbolic r_e and its symbolic domain")
  else:
    r_e_symb_domain = islpy.BasicSet.universe(r_e.get_space().params())

  inverse_op_map = {"+": "-", "*": "//"}

  prog = copy.deepcopy(prog)

  reduction = prog.get_statement_by_id(stmt_id)
  param_space = r_e.get_space().params()
  D_E = reduction.domain.align_params(param_space)
  if D_E.n_basic_set() > 1:
    raise ValueError("can only transform reduction with a BasicSet domain")

  r_e_map = islpy.BasicMap.from_multi_aff(r_e)
  r_e_rev_map = r_e_map.reverse()
  del r_e

  D_E = D_E.align_params(param_space)

  D_E_p = D_E.apply(r_e_rev_map)

  lhs_proj_map = reduction.lhs_proj_map.align_params(param_space)

  D_add = D_E.subtract(D_E_p).apply(lhs_proj_map)
  D_sub = D_E_p.subtract(D_E).apply(lhs_proj_map)
  D_int = D_E.intersect(D_E_p).apply(lhs_proj_map)

  if D_int.is_empty():
    raise ValueError("no reuse if intersection is empty")

  lhs_space_tmp_var_names = ir.tmp_vars(num=reduction.lhs_domain.n_dim())

  # Project r_e_map onto lhs space
  r_e_lhs_map = r_e_map.apply_domain(lhs_proj_map).apply_range(lhs_proj_map)
  if r_e_lhs_map.is_identity():
    raise ValueError("shift must not be in ker(f_p)")
  r_e_lhs_ma = islpy.PwMultiAff.from_map(r_e_lhs_map)
  assert r_e_lhs_ma.n_piece() == 1, ("Something is wrong with r_f"
                                     "it should only have 1 piece")
  r_e_lhs_ma = r_e_lhs_ma.as_multi_aff()

  X_add_name = ir.ArrayID(reduction.lhs_array_name + "_add")
  X_add_domain = D_E.subtract(D_E_p)
  X_add_domain = X_add_domain.intersect_params(r_e_symb_domain).make_disjoint()
  X_add_access = _make_simple_subscript_ast(X_add_name,
                                            lhs_space_tmp_var_names,
                                            store=False)
  if not X_add_domain.is_empty():
    for X_add_domain_basic in X_add_domain.get_basic_sets():
      X_add_stmt = ir.Statement(X_add_domain_basic, reduction.param_space_names,
                                reduction.domain_space_names, X_add_name,
                                reduction.rhs, reduction.lhs_proj, reduction.op,
                                reduction.non_affine_constraints,
                                reduction.histograms)
      prog.add_statement(X_add_stmt)

  X_sub_name = ir.ArrayID(reduction.lhs_array_name + "_sub")
  X_sub_domain = D_int.apply(lhs_proj_map.reverse()).intersect(
      D_E_p.subtract(D_E)).apply(r_e_map)
  X_sub_domain = X_sub_domain.intersect_params(r_e_symb_domain).make_disjoint()
  X_sub_access = _make_simple_subscript_ast(X_sub_name,
                                            lhs_space_tmp_var_names,
                                            store=False)
  if not X_sub_domain.is_empty():
    if reduction.op not in inverse_op_map:
      raise ValueError("Operator must have an inverse to have non-empty D_sub")
    # No need to check for n_pieces == 1 again here
    r_rev_f = islpy.PwMultiAff.from_map(r_e_lhs_map.reverse()).as_multi_aff()
    for X_sub_domain_basic in X_sub_domain.get_basic_sets():
      X_sub_stmt = ir.Statement(X_sub_domain_basic, reduction.param_space_names,
                                reduction.domain_space_names, X_sub_name,
                                reduction.rhs,
                                r_rev_f.pullback_multi_aff(reduction.lhs_proj),
                                reduction.op, reduction.non_affine_constraints,
                                reduction.histograms)
      prog.add_statement(X_sub_stmt)

  index_args = ir.multi_aff_to_ast(r_e_lhs_ma, lhs_space_tmp_var_names)
  shifted_X_access = _make_subscript_ast(reduction.lhs_array_name,
                                         index_args,
                                         store=False)

  def handle_1_case(D, rhs_expression_f: Callable[[], ast.AST]):
    D = D.intersect_params(r_e_symb_domain)
    if not D.is_empty():
      stmt = ir.Statement(
          D,
          reduction.param_space_names,
          lhs_space_tmp_var_names,
          reduction.lhs_array_name,
          ast.Expression(body=rhs_expression_f()),
          lhs_proj=islpy.MultiAff.identity_on_domain_space(
              reduction.lhs_domain.get_space()),
          op=None,
          non_affine_constraints=reduction.non_affine_constraints)
      prog.add_statement(stmt)

  op_to_ast_map = {
      "+": ast.Add(),
      "-": ast.Sub(),
      "*": ast.Mult(),
      "//": ast.FloorDiv()
  }
  op_ast = op_to_ast_map[reduction.op]
  inv_op_ast = op_to_ast_map[inverse_op_map[reduction.op]]
  # Handle 5 cases for incremental computation

  handle_1_case(D_add.subtract(D_int), lambda: X_add_access)

  handle_1_case(D_int.subtract(D_add.union(D_sub)), lambda: shifted_X_access)

  handle_1_case(
      D_add.intersect(D_int.subtract(D_sub)),
      lambda: ast.BinOp(left=X_add_access, op=op_ast, right=shifted_X_access))

  handle_1_case(
      D_sub.intersect(D_int.subtract(D_add)), lambda: ast.BinOp(
          left=shifted_X_access, op=inv_op_ast, right=X_sub_access))

  handle_1_case(
      D_add.intersect(D_int.intersect(D_sub)), lambda: ast.BinOp(
          left=ast.BinOp(left=X_add_access, op=op_ast, right=shifted_X_access),
          op=inv_op_ast,
          right=X_sub_access))

  if is_symbolic_st:
    # If we are working symbolically, then the original reduction is kept
    # if the reuse vector is a zero vector
    symb_eq_zero = islpy.BasicSet.universe(r_e_symb_domain.get_space())
    for i in range(D_E.n_dim()):
      symb_eq_zero = symb_eq_zero.fix_val(islpy.dim_type.param,
                                          symb_eq_zero.n_param() - i - 1, 0)
    reduction.domain = D_E.intersect_params(symb_eq_zero)
    reduction.lhs_proj = reduction.lhs_proj.align_params(param_space)
  return prog


LhsShareSpaceMapType = Dict[ir.VarID, islpy.BasicSet]
RhsShareSpaceMapType = Dict[int, islpy.BasicSet]


class ShareSpaceCollector(ir.AffineExprWalker):

  def __init__(
      self,
      ctx: islpy.Context,
      domain_space_names: List[ir.VarID],
      param_space_names: List[ir.VarID],
      affine_annotation: Dict[ast.AST,
                              ir.AffineExpresionCollector.ExpressionKind],
      reads: Set[ast.AST],
      lhs_share_space_map: LhsShareSpaceMapType,
      node: Optional[ast.Expression] = None,
      *args,
      **kwargs):
    self.share_space = islpy.Space.create_from_names(ctx,
                                                     set=domain_space_names,
                                                     params=param_space_names)
    self.default_share_space_set = basic_set_zero(self.share_space)
    self.lhs_share_space_map = defaultdict(lambda: self.default_share_space_set,
                                           lhs_share_space_map)
    self.share_space_set = islpy.BasicSet.universe(self.share_space)
    ir.AffineExprWalker.__init__(self,
                                 ctx,
                                 domain_space_names,
                                 param_space_names,
                                 affine_annotation,
                                 reads,
                                 node=node,
                                 **kwargs)

  def handle_identity_affine_expr(self):
    node = self.cur_node
    aff = ir.ast_to_aff(node, self.ctx, self.domain_space_names,
                        self.param_space_names)
    share_space_map = aff.eq_map(aff).get_basic_maps()[0]
    share_space_set = self.default_share_space_set.apply(share_space_map)
    share_space_set = isl_utils.compute_lineality_space(share_space_set)
    self.share_space_set = self.share_space_set.intersect(share_space_set)

  def handle_subscript_affine_expr(self):
    read = self.cur_node
    read_map = ir.read_ast_to_map(read, self.ctx, self.domain_space_names,
                                  self.param_space_names,
                                  self.affine_annotation)
    if read.value.id not in self.lhs_share_space_map:
      self.lhs_share_space_map[read.value.id] = basic_set_zero(
          read_map.range().get_space())
    array_ref_share_space_set = self.lhs_share_space_map[read.value.id]

    share_space_set = array_ref_share_space_set.apply(read_map.reverse())
    share_space_set = isl_utils.compute_lineality_space(share_space_set)
    self.share_space_set = self.share_space_set.intersect(share_space_set)


def compute_share_space_for_statement(
    stmt: ir.Statement, declared_lhs_symbols: Set[ir.VarID],
    share_space_map: LhsShareSpaceMapType) -> islpy.BasicSet:
  affine_expr_collector = ir.AffineExpresionCollector(stmt.domain_space_names,
                                                      stmt.rhs)
  reads = schedule.ASTCollectRead(stmt.rhs, declared_lhs_symbols).reads
  share_space_collector = ShareSpaceCollector(stmt.domain.get_ctx(),
                                              stmt.domain_space_names,
                                              stmt.param_space_names,
                                              affine_expr_collector.annotation,
                                              reads,
                                              share_space_map,
                                              node=stmt.rhs)
  return share_space_collector.share_space_set


def compute_reduction_lhs_share_space(
    stmt: ir.Statement, rhs_share_space: islpy.BasicSet) -> islpy.BasicSet:
  non_boundary_constraints = isl_utils.compute_non_boundary_constraint(
      stmt.domain, stmt.lhs_proj)
  valid_share = isl_utils.bs_from_kernel_of_constraints(
      rhs_share_space.get_space(), non_boundary_constraints)
  return rhs_share_space.intersect(valid_share).apply(stmt.lhs_proj_map)


def compute_share_space_one_pass(
    prog: ir.Program,
    lhs_share_space_map: LhsShareSpaceMapType,
) -> Tuple[LhsShareSpaceMapType, RhsShareSpaceMapType]:
  """Computes reuse space for program by traversing top-down through statements.
  """
  lhs_share_space_map = dict(lhs_share_space_map)
  updated_lhs_symbols = set()
  rhs_share_space_map = {}
  declared_lhs_symbols = {
      stmt.lhs_array_name for stmt in prog.statements.values()
  }
  for stmt_id, _, stmt in prog.iter_named_statements():
    rs = compute_share_space_for_statement(stmt, declared_lhs_symbols,
                                           lhs_share_space_map)

    rhs_share_space_map[stmt_id] = rs
    if stmt.is_reduction:
      lhs_rs = compute_reduction_lhs_share_space(stmt, rs)
      # lineality_space = isl_utils.compute_lineality_space(stmt.domain)
      # lhs_rs = rs.intersect(lineality_space).apply(stmt.lhs_proj_map)
    else:
      lhs_rs = rs

    if stmt.lhs_array_name not in updated_lhs_symbols:
      lhs_share_space_map[stmt.lhs_array_name] = lhs_rs
      updated_lhs_symbols.add(stmt.lhs_array_name)
    else:
      lhs_share_space_map[stmt.lhs_array_name] = lhs_share_space_map[
          stmt.lhs_array_name].intersect(lhs_rs)
  return lhs_share_space_map, rhs_share_space_map


def compute_share_space(
    prog: ir.Program) -> Tuple[LhsShareSpaceMapType, RhsShareSpaceMapType]:
  """Computes share space for program.

  The routine iteratively invokes `compute_share_space_one_pass`
  until convergence.

  Args:
    prog: input program

  Returns:
    A tuple of mapping for LHS reuse space and RHS reuse space.
  """
  lhs_share_space_map, rhs_share_space_map = {}, {}
  changed = True
  while changed:
    new_lhs_share_space_map, new_rhs_share_space_map = compute_share_space_one_pass(
        prog, lhs_share_space_map)
    changed = (new_lhs_share_space_map, new_rhs_share_space_map) != (
        lhs_share_space_map, rhs_share_space_map)
    lhs_share_space_map, rhs_share_space_map = (new_lhs_share_space_map,
                                                new_rhs_share_space_map)
  return lhs_share_space_map, rhs_share_space_map


def compute_reuse_set_for_statement(
    prog: ir.Program, stmt_id: int,
    share_space_map: RhsShareSpaceMapType) -> islpy.MultiVal:
  """Computes a Set of valid reuse directions for statement.

  Note that the returned the reuse_set always does NOT contain the zero point.
  This is because proj_kernel always contains identity (zero point), and we
  subtracted proj_kernel off from the reuse_set.
  """
  share_space = share_space_map[stmt_id]
  stmt = prog.get_statement_by_id(stmt_id)
  proj_kernel = isl_utils.compute_null_space(stmt.lhs_proj)
  effective_linear_space = isl_utils.compute_effective_linear_space(stmt.domain)
  reuse_set = share_space.intersect(effective_linear_space).subtract(
      proj_kernel)
  return reuse_set


def sample_non_zero_reuse_vector_for_statement(
    prog: ir.Program, stmt_id: int,
    share_space_map: RhsShareSpaceMapType) -> islpy.MultiVal:
  """Samples a non-zero reuse vector for statement."""
  non_zero_reuse_set = compute_reuse_set_for_statement(prog, stmt_id,
                                                       share_space_map)
  if non_zero_reuse_set.is_empty():
    raise ValueError("Empty reuse set")
  point = non_zero_reuse_set.sample_point()
  return isl_utils.point_to_multi_val(point)


def sample_non_zero_reuse_vector_for_statement_with_correct_dependence(
    prog: ir.Program, stmt_id: int, share_space_map: RhsShareSpaceMapType,
    barrier_map: schedule.BarrierMap, sched: islpy.Schedule) -> islpy.MultiVal:
  """Samples non zero reuse vector that satisfies the original schedule.

  Args:
    prog: input program with injected barrier statements.
    stmt_id: target statement this ST is applying to.
    share_space_map: reuse space mapping for RHS expressions.
    barrier_map: barrier map for the injected statements.
    sched: ISL schedule for `prog`

  Returns:
    a reuse direction that is valid with respect to the schedule.
  """
  r_e = sample_non_zero_reuse_vector_for_statement(prog, stmt_id,
                                                   share_space_map)
  schedule_map = sched.get_map()
  barrier_stmt_name = prog.stmt_name(barrier_map[stmt_id])
  stmt = prog.get_statement_by_id(stmt_id)
  r_e_bs = islpy.BasicSet.from_multi_aff(
      islpy.MultiAff.multi_val_on_space(r_e.get_domain_space(), r_e))
  r_e_lhs = r_e_bs.apply(stmt.lhs_proj_map).set_tuple_name(barrier_stmt_name)
  test_vec = r_e_lhs.apply(schedule_map)
  test_vec_bs_list = test_vec.get_basic_set_list()
  if test_vec_bs_list.n_basic_set() != 1:
    raise ValueError("Invalid schedule")
  test_vec = test_vec_bs_list.get_at(0)
  if not test_vec.is_singleton():
    raise ValueError("Invalid schedule")
  # Set params to 1 -- this assumes that all parameters are positive
  # TODO(camyang) fix this, params and const's coefficients should be 0
  for i in range(test_vec.n_param()):
    test_vec = test_vec.fix_val(islpy.dim_type.param, i,
                                islpy.Val.one(test_vec.get_ctx()))
  test_point = test_vec.sample_point()  # cast to point
  for i in range(test_point.get_space().dim(islpy.dim_type.set)):
    coord_val = test_point.get_coordinate_val(islpy.dim_type.set, i).to_python()
    if coord_val != 0:
      dep_satisfied = coord_val < 0
      break
  if not dep_satisfied:
    r_e = r_e.neg()
  return r_e


if __name__ == "__main__":
  prog = ir.Program.read_from_string("""
  N M
  A[i] += B[j]     # { [i, j] : 0 <= i < N & 0 <= j < i} ;
  B[i] = f(A[i])   # { [i] : 0 <= i < N };
  """)
  _, share_space_map = compute_share_space(prog)
  stmt_id = 0
  # r_e = sample_non_zero_reuse_vector_for_statement(prog, stmt_id,
  #                                                  share_space_map)
  # print(r_e)
  # new_prog1 = simplification_transformation(prog, stmt_id, r_e)
  barrier_prog, barrier_map = schedule.inject_reduction_barrier_statements(prog)
  # new_prog, barrier_map = prog, None
  sched = schedule.schedule_program(barrier_prog)
  isl_ast = schedule.schedule_isl_ast_gen(prog, sched, barrier_map=barrier_map)
  cgen_ast = code_gen.isl_ast_code_gen(prog, isl_ast)
  print(astor.to_source(cgen_ast))

  # Perform ST
  r_e = sample_non_zero_reuse_vector_for_statement_with_correct_dependence(
      barrier_prog, stmt_id, share_space_map, barrier_map, sched)
  st_prog = simplification_transformation(prog, stmt_id, r_e)

  # Generate ST transformed code
  barrier_st_prog, barrier_map = schedule.inject_reduction_barrier_statements(
      st_prog)
  sched = schedule.schedule_program(barrier_st_prog)
  isl_ast = schedule.schedule_isl_ast_gen(st_prog,
                                          sched,
                                          barrier_map=barrier_map)
  cgen_ast = code_gen.isl_ast_code_gen(st_prog, isl_ast)
  # print(astor.dump_tree(cgen_ast))
  print(astor.to_source(cgen_ast))

"""Simplifcation Transformation."""

from typing import Callable, List, Dict, Set, Optional, Tuple

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


def _make_subscript_ast(lhs_name: ir.VarID, rhs_asts: List[ast.AST]):
  if len(rhs_asts) == 1:
    rhs = rhs_asts[0]
  else:
    rhs = ast.Tuple(elts=rhs_asts)
  return ast.Subscript(value=ast.Name(id=lhs_name, ctx=ast.Store()),
                       slice=ast.Index(value=rhs))


def _make_simple_subscript_ast(lhs_name: ir.VarID, rhs_names: List[ir.VarID]):
  rhs_asts = [ast.Name(id=name, ctx=ast.Load()) for name in rhs_names]
  return _make_subscript_ast(lhs_name, rhs_asts)


def simplification_transformation(prog: ir.Program,
                                  stmt_id: ir.Program.StatementID,
                                  r_e: islpy.MultiVal) -> ir.Program:
  """Apply Simplification Transformation with given reuse direction."""

  inverse_op_map = {"+": "-", "*": "//"}

  prog = copy.deepcopy(prog)

  reduction = prog.get_statement_by_id(stmt_id)
  D_E = reduction.domain
  if D_E.n_basic_set() > 1:
    raise ValueError("can only transform reduction with a BasicSet domain")

  lhs_proj_map = reduction.lhs_proj_map

  r_e = islpy.MultiAff.multi_val_on_space(r_e.get_space(), r_e)
  r_e = r_e.add(r_e.identity_multi_aff())
  r_e = r_e.align_params(D_E.get_space())
  r_e_map = islpy.BasicMap.from_multi_aff(r_e)

  r_e_rev_map = r_e_map.reverse()

  D_E_p = D_E.apply(r_e_rev_map)

  D_add = D_E.subtract(D_E_p).apply(lhs_proj_map)
  D_sub = D_E_p.subtract(D_E).apply(lhs_proj_map)
  D_int = D_E.intersect(D_E_p).apply(lhs_proj_map)

  if D_int.is_empty():
    raise ValueError("no reuse if intersection is empty")

  lhs_space_tmp_var_names = ir.tmp_vars(num=reduction.lhs_domain.n_dim())

  # Project r_e_map onto lhs space
  r_f_map = r_e_map.apply_domain(lhs_proj_map).apply_range(lhs_proj_map)
  if r_f_map.is_identity():
    raise ValueError("shift must not be in ker(f_p)")
  r_f = islpy.PwMultiAff.from_map(r_f_map)
  assert r_f.n_piece() == 1, ("Something is wrong with r_f"
                              "it should only have 1 piece")
  r_f = r_f.as_multi_aff()
  # No need to check again here
  r_rev_f = islpy.PwMultiAff.from_map(r_f_map.reverse()).as_multi_aff()

  X_add_name = ir.ArrayID(reduction.lhs_array_name + "_add")
  X_add_domain = D_E.subtract(D_E_p)
  X_add_access = _make_simple_subscript_ast(X_add_name, lhs_space_tmp_var_names)

  if not X_add_domain.is_empty():
    X_add_domain = X_add_domain.make_disjoint()
    for X_add_domain_basic in X_add_domain.get_basic_sets():
      X_add_stmt = ir.Statement(X_add_domain_basic, reduction.param_space_names,
                                reduction.domain_space_names, X_add_name,
                                reduction.rhs, reduction.lhs_proj, reduction.op,
                                reduction.non_affine_constraints)
      prog.add_statement(X_add_stmt)

  X_sub_name = ir.ArrayID(reduction.lhs_array_name + "_sub")
  X_sub_domain = D_int.apply(lhs_proj_map.reverse()).intersect(
      D_E_p.subtract(D_E)).apply(r_e_map)
  X_sub_access = _make_simple_subscript_ast(X_sub_name, lhs_space_tmp_var_names)

  if not X_sub_domain.is_empty():
    if reduction.op not in inverse_op_map:
      raise ValueError("Operator must have an inverse to have non-empty D_sub")
    X_sub_domain = X_sub_domain.make_disjoint()
    for X_sub_domain_basic in X_sub_domain.get_basic_sets():
      X_sub_stmt = ir.Statement(X_sub_domain_basic, reduction.param_space_names,
                                reduction.domain_space_names, X_sub_name,
                                reduction.rhs,
                                r_rev_f.pullback_multi_aff(reduction.lhs_proj),
                                reduction.op, reduction.non_affine_constraints)
      prog.add_statement(X_sub_stmt)

  index_args = ir.multi_aff_to_ast(r_f, lhs_space_tmp_var_names)
  shifted_X_access = _make_subscript_ast(reduction.lhs_array_name, index_args)

  def handle_1_case(D, rhs_expression_f: Callable[[], ast.AST]):
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

  prog.remove_statement(stmt_id)

  return prog


LhsReuseSpaceMapType = Dict[ir.VarID, islpy.BasicSet]
RhsReuseSpaceMapType = Dict[int, islpy.BasicSet]


class ReuseSpaceCollector(astor.TreeWalk):

  def __init__(
      self,
      ctx: islpy.Context,
      domain_space_names: List[ir.VarID],
      param_space_names: List[ir.VarID],
      affine_annotation: Dict[ast.AST,
                              ir.AffineExpresionCollector.ExpressionKind],
      reads: Set[ast.AST],
      lhs_reuse_space_map: LhsReuseSpaceMapType,
      node: Optional[ast.Expression] = None,
      *args,
      **kwargs):
    self.ctx = ctx
    self.domain_space_names = domain_space_names
    self.param_space_names = param_space_names
    self.reuse_space = islpy.Space.create_from_names(ctx,
                                                     set=domain_space_names,
                                                     params=param_space_names)
    self.default_reuse_space_set = basic_set_zero(self.reuse_space)
    self.lhs_reuse_space_map = defaultdict(lambda: self.default_reuse_space_set,
                                           lhs_reuse_space_map)
    self.reads = reads
    self.reuse_space_set = islpy.BasicSet.universe(self.reuse_space)
    self.affine_annotation = affine_annotation
    astor.TreeWalk.__init__(self, node=node, *args, **kwargs)

  def pre_any_node(self):
    node = self.cur_node
    if ((isinstance(node, ast.AST) and self.affine_annotation[node] !=
         ir.AffineExpresionCollector.ExpressionKind.non_affine) and
        (not isinstance(self.parent, ast.AST) or
         self.affine_annotation[self.parent] ==
         ir.AffineExpresionCollector.ExpressionKind.non_affine)):
      aff = ir.ast_to_aff(node, self.ctx, self.domain_space_names,
                          self.param_space_names)
      reuse_space_map = aff.eq_map(aff).get_basic_maps()[0]
      reuse_space_set = self.default_reuse_space_set.apply(reuse_space_map)
      self.reuse_space_set = self.reuse_space_set.intersect(reuse_space_set)
      return True

  def post_any_node(self):
    pass

  class PatchedDict(defaultdict):

    def get(self, key, default=None):
      if default is not None:
        return super().get(key, default)
      else:
        return self[key]

  def setup(self):
    astor.TreeWalk.setup(self)
    self.pre_handlers = ReuseSpaceCollector.PatchedDict(
        lambda: self.pre_any_node, self.pre_handlers)
    self.post_handlers = ReuseSpaceCollector.PatchedDict(
        lambda: self.post_any_node, self.post_handlers)

  def pre_Subscript(self):
    if self.cur_node in self.reads:
      read = self.cur_node
      array_ref_reuse_space_set = self.lhs_reuse_space_map[read.value.id]
      read_map = ir.read_ast_to_map(read, self.ctx, self.domain_space_names,
                                    self.param_space_names,
                                    self.affine_annotation)
      reuse_space_set = array_ref_reuse_space_set.apply(read_map.reverse())
      self.reuse_space_set = self.reuse_space_set.intersect(reuse_space_set)
      return True


def compute_reuse_space_for_statement(
    stmt: ir.Statement, declared_lhs_symbols: Set[ir.VarID],
    reuse_space_map: LhsReuseSpaceMapType) -> islpy.BasicSet:
  affine_expr_collector = ir.AffineExpresionCollector(stmt.domain_space_names,
                                                      stmt.rhs)
  reads = schedule.ASTCollectRead(stmt.rhs, declared_lhs_symbols).reads
  reuse_space_collector = ReuseSpaceCollector(stmt.domain.get_ctx(),
                                              stmt.domain_space_names,
                                              stmt.param_space_names,
                                              affine_expr_collector.annotation,
                                              reads,
                                              reuse_space_map,
                                              node=stmt.rhs)
  return reuse_space_collector.reuse_space_set


def compute_reduction_lhs_reuse_space(
    stmt: ir.Statement, rhs_reuse_space: islpy.BasicSet) -> islpy.BasicSet:
  non_boundary_constraints = isl_utils.compute_non_boundary_constraint(
      stmt.domain, stmt.lhs_proj)
  valid_reuse = isl_utils.bs_from_kernel_of_constraints(
      rhs_reuse_space.get_space(), non_boundary_constraints)
  return rhs_reuse_space.intersect(valid_reuse).apply(stmt.lhs_proj_map)


def compute_reuse_space_one_pass(
    prog: ir.Program,
    lhs_reuse_space_map: LhsReuseSpaceMapType,
) -> Tuple[LhsReuseSpaceMapType, RhsReuseSpaceMapType]:
  updated_lhs_symbols = set()
  rhs_reuse_space_map = {}
  declared_lhs_symbols = {
      stmt.lhs_array_name for stmt in prog.statements.values()
  }
  for stmt_id, _, stmt in prog.iter_named_statements():
    rs = compute_reuse_space_for_statement(stmt, declared_lhs_symbols,
                                           lhs_reuse_space_map)
    rhs_reuse_space_map[stmt_id] = rs
    if stmt.is_reduction:
      lhs_rs = compute_reduction_lhs_reuse_space(stmt, rs)
      # lineality_space = isl_utils.compute_lineality_space(stmt.domain)
      # lhs_rs = rs.intersect(lineality_space).apply(stmt.lhs_proj_map)
    else:
      lhs_rs = rs

    if stmt.lhs_array_name not in updated_lhs_symbols:
      lhs_reuse_space_map[stmt.lhs_array_name] = lhs_rs
      updated_lhs_symbols.add(stmt.lhs_array_name)
    else:
      lhs_reuse_space_map[stmt.lhs_array_name] = lhs_reuse_space_map[
          stmt.lhs_array_name].intersect(lhs_rs)
  return lhs_reuse_space_map, rhs_reuse_space_map


def compute_reuse_space(
    prog: ir.Program) -> Tuple[LhsReuseSpaceMapType, RhsReuseSpaceMapType]:
  lhs_reuse_space_map, rhs_reuse_space_map = {}, {}
  changed = True
  while changed:
    lhs_reuse_space_map, new_rhs_reuse_space_map = compute_reuse_space_one_pass(
        prog, lhs_reuse_space_map)
    changed = new_rhs_reuse_space_map == rhs_reuse_space_map
    rhs_reuse_space_map = new_rhs_reuse_space_map
  return lhs_reuse_space_map, rhs_reuse_space_map


def sample_non_zero_vector_from_reuse_set(
    reuse_set: islpy.Set) -> islpy.MultiVal:
  point = reuse_set.subtract(isl_utils.basic_set_zero(
      reuse_set.get_space())).sample_point()
  return isl_utils.point_to_multi_val(point)


def sample_non_zero_reuse_vector_for_statement(
    prog: ir.Program, stmt_id: int,
    reuse_space_map: RhsReuseSpaceMapType) -> islpy.MultiVal:
  reuse_set = reuse_space_map[stmt_id]
  stmt = prog.get_statement_by_id(stmt_id)
  proj_kernel = isl_utils.compute_proj_kernel(stmt.lhs_proj)
  return sample_non_zero_vector_from_reuse_set(reuse_set.subtract(proj_kernel))


if __name__ == "__main__":
  prog = ir.Program.read_from_string("""
  N M
  A[i] += 1     # { [i, j, k] : 0 <= i < N & 0 <= j < M & 0 <= k < M } ;
  """)
  _, reuse_space_map = compute_reuse_space(prog)
  stmt_id = 0
  r_e = sample_non_zero_reuse_vector_for_statement(prog, stmt_id,
                                                   reuse_space_map)
  print(r_e)
  new_prog1 = simplification_transformation(prog, stmt_id, r_e)
  new_prog2, barrier_map = schedule.inject_reduction_barrier_statements(
      new_prog1)
  # new_prog, barrier_map = prog, None
  sched = schedule.schedule_program(new_prog2)
  isl_ast = schedule.schedule_isl_ast_gen(new_prog2,
                                          sched,
                                          barrier_map=barrier_map)
  cgen_ast = code_gen.isl_ast_code_gen(new_prog1, isl_ast)
  # print(astor.dump_tree(cgen_ast))
  print(astor.to_source(cgen_ast))

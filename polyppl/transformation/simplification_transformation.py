"""Simplifcation Transformation."""

import islpy

from typing import Callable, List

import copy
import ast
import astor

from polyppl.isl_utils import aff_align_in_ids
import polyppl.ir as ir
import polyppl.schedule as schedule
import polyppl.code_gen as code_gen


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
                                  r_e: islpy.MultiAff) -> ir.Program:
  """Apply Simplification Transformation with given reuse direction."""

  inverse_op_map = {"+": "-", "*": "//"}

  prog = copy.deepcopy(prog)

  reduction = prog.get_statement_by_id(stmt_id)
  D_E = reduction.domain
  if D_E.n_basic_set() > 1:
    raise ValueError("can only transform reduction with a BasicSet domain")

  lhs_proj_map = reduction.lhs_proj_map

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

  X_add_name = ir.ArrayID(reduction.lhs_array_name + "_add")
  X_add_domain = D_E.subtract(D_E_p)
  X_add_access = _make_simple_subscript_ast(X_add_name, lhs_space_tmp_var_names)

  if not X_add_domain.is_empty():
    for X_add_domain_basic in X_add_domain.get_basic_sets():
      X_add_stmt = ir.Statement(X_add_domain_basic, reduction.param_space_names,
                                reduction.domain_space_names, X_add_name,
                                reduction.rhs, reduction.lhs_proj, reduction.op,
                                reduction.non_affine_constraints)
      prog.add_statement(X_add_stmt)

  X_sub_name = ir.ArrayID(reduction.lhs_array_name + "_sub")
  X_sub_domain = D_int.apply(lhs_proj_map.reverse()).intersect(
      D_E_p.subtract(D_E))
  X_sub_access = _make_simple_subscript_ast(X_sub_name, lhs_space_tmp_var_names)

  if not X_sub_domain.is_empty():
    if reduction.op not in inverse_op_map:
      raise ValueError("Operator must have an inverse to have non-empty D_sub")
    for X_sub_domain_basic in X_sub_domain.get_basic_sets():
      X_sub_stmt = ir.Statement(X_sub_domain_basic, reduction.param_space_names,
                                reduction.domain_space_names, X_sub_name,
                                reduction.rhs, reduction.lhs_proj, reduction.op,
                                reduction.non_affine_constraints)
      prog.add_statement(X_sub_stmt)

  r_f_map = r_e_map.apply_domain(lhs_proj_map).apply_range(lhs_proj_map)
  if r_f_map.is_identity():
    raise ValueError("shift must not be in ker(f_p)")
  r_f = islpy.PwMultiAff.from_map(r_f_map)
  assert r_f.n_piece() == 1, ("Something is wrong with r_f"
                              "it should only have 1 piece")
  r_f = r_f.as_multi_aff()
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


if __name__ == "__main__":
  prog = ir.Program.read_from_string("""
  N
  A[i] += f(B[j])     # { [i, j] : 0 <= i < N & 0 <= j < i } ;
  """)
  new_prog1 = simplification_transformation(
      prog, 0, islpy.MultiAff.read_from_str(prog.ctx, "{ [i, j] -> [i-1, j] }"))
  new_prog2, barrier_map = schedule.inject_reduction_barrier_statements(
      new_prog1)
  # new_prog, barrier_map = prog, None
  schedule = schedule.schedule_program(new_prog2)
  isl_ast = schedule.schedule_isl_ast_gen(new_prog2,
                                          schedule,
                                          barrier_map=barrier_map)
  cgen_ast = code_gen.isl_ast_code_gen(new_prog1, isl_ast)
  # print(astor.dump_tree(cgen_ast))
  print(astor.to_source(cgen_ast))

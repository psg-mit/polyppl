import islpy

from typing import Callable

import polyppl.ir as ir
from polyppl.isl_utils import aff_align_param_ids, tmp_vars


class SimplifyingReduction(object):

  def __init__(self, stmt_id, r_e: islpy.BasicMap):
    self.stmt_id = stmt_id
    self.r_e = r_e

  def apply(self, prog: ir.Program) -> ir.Program:
    inverse_op_map = {"+": "-", "*": "/"}
    reduction = prog.get_statement_by_id(self.stmt_id)
    r_e = self.r_e
    D_E = reduction.domain
    f_p = reduction.proj

    r_e = r_e.align_params(D_E.get_space())
    assert r_e.is_bijective(), "shift vector must be a function"

    r_e_rev = r_e.reverse()

    D_E_p = D_E.apply(r_e_rev)

    D_add = D_E.subtract(D_E_p).apply(f_p)
    D_sub = D_E_p.subtract(D_E).apply(f_p)
    D_int = D_E.intersect(D_E_p).apply(f_p)

    assert not D_int.is_empty(), "no reuse if intersection is empty"

    lhs_space_tmp_var_names = tmp_vars(reduction.lhs_domain.n_dim())

    X_add_name = ir.ArrayID(reduction.lhs_array_name + "_add")
    X_add_domain = D_E.subtract(D_E_p)
    X_add_access = ir.AccessExpression(
        X_add_name, map(ir.RefExpression, lhs_space_tmp_var_names))
    if not X_add_domain.is_empty():
      X_add_stmt = ir.Statement(X_add_domain, reduction.param_space_names,
                                reduction.domain_space_names, X_add_name,
                                reduction.expr, reduction.lhs_proj,
                                reduction.op, reduction.non_affine_constraints)
      prog.add_stmt(X_add_stmt)

    X_sub_name = ir.ArrayID(reduction.lhs_array_name + "_sub")
    X_sub_domain = D_int.apply(f_p.reverse()).intersect(D_E_p.subtract(D_E))
    X_sub_access = ir.AccessExpression(
        X_sub_name, map(ir.RefExpression, lhs_space_tmp_var_names))
    if not X_sub_domain.is_empty():
      assert reduction.op in inverse_op_map, \
        "Operator must have an inverse to have non-empty D_sub"
      X_sub_stmt = ir.Statement(X_sub_domain, reduction.param_space_names,
                                reduction.domain_space_names, X_sub_name,
                                reduction.expr, reduction.lhs_proj,
                                inverse_op_map[reduction.op],
                                reduction.non_affine_constraints)
      prog.add_stmt(X_sub_stmt)

    r_f_map = r_e.apply_domain(f_p).apply_range(f_p)
    assert not r_f_map.is_identity(), "shift must not be in ker(f_p)"
    r_f = islpy.MultiPwAff.from_pw_multi_aff(
        islpy.PwMultiAff.from_map(r_f_map))  # TODO: weird API in ISL
    r_f = aff_align_param_ids(r_f, lhs_space_tmp_var_names)
    index_args = []
    for i in range(r_f.dim(islpy.dim_type.out)):
      aff = r_f.get_pw_aff(i).get_pieces()[0][1]
      index_args.append(ir.AffineExpression.from_isl_aff_exp(aff))
    shifted_X_access = ir.AccessExpression(reduction.lhs_array_name, index_args)

    def handle_1_case(D, rhs_expression_f: Callable[[], ir.Expression]):
      if not D.is_empty():
        stmt = ir.Statement(
            D,
            reduction.param_space_names,
            lhs_space_tmp_var_names,
            reduction.lhs_array_name,
            rhs_expression_f(),
            lhs_proj=None,
            op=None,
            non_affine_constraints=reduction.non_affine_constraints)
        prog.add_stmt(stmt)

    # Handle 5 cases for incremental computation

    handle_1_case(D_add.subtract(D_int), lambda: X_add_access)

    handle_1_case(D_int.subtract(D_add.union(D_sub)), lambda: shifted_X_access)

    handle_1_case(
        D_add.intersect(D_int.subtract(D_sub)),
        lambda: ir.OpExpression(reduction.op, [X_add_access, shifted_X_access]))

    handle_1_case(
        D_sub.intersect(D_int.subtract(D_add)), lambda: ir.OpExpression(
            inverse_op_map[reduction.op], [shifted_X_access, X_sub_access]))

    handle_1_case(
        D_add.intersect(D_int.intersect(D_sub)),
        lambda: ir.OpExpression(inverse_op_map[reduction.op], [
            ir.OpExpression(reduction.op, [X_add_access, shifted_X_access]),
            X_sub_access
        ]))

    prog.remove_stmt(self.stmt_id)

    return prog

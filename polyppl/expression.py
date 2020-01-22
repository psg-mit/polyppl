"""!!! This module is deprecated. !!!

This module contains the old expression classes for ir.py .
Current IR keeps a python ast as the expression class, so the classes below
have been deprecated, but kept here in case of future code reuse.
"""
import warnings
warnings.warn("This module ({}) is deprecated.".format(__file__))

from typing import List, Sequence

from dataclasses import dataclass
import itertools

from pampy import match, _
import islpy

from polyppl.ir import VarID, OpID, ArrayID, tmp_var_allocator

################################################################################
#    BEGIN Expression
################################################################################


@dataclass
class Expression:
  pass


@dataclass
class OpExpression(Expression):
  op: OpID
  args: List[Expression]


@dataclass
class AffineExpression(OpExpression):

  @staticmethod
  def from_isl_aff_exp(aff: islpy.Aff) -> "AffineExpression":
    coeffs = aff.get_coefficients_by_name(islpy.dim_type.in_)
    exp = ConstExpression(coeffs.pop(1).to_python())
    for name, coeff in coeffs.items():
      coeff = coeff.to_python()
      if coeff > 0:
        exp = AffineExpression("+", [exp, RefExpression(name)])
      else:
        exp = AffineExpression("-", [exp, RefExpression(name)])
    return exp


@dataclass
class AccessExpression(Expression):
  name: ArrayID
  args: List[AffineExpression]


@dataclass
class ConstExpression(Expression):
  val: int


@dataclass
class RefExpression(Expression):
  name: VarID


def get_freevars(exp: Expression) -> Sequence[VarID]:

  def inner(exp, result: Sequence[VarID]):
    return match(
        exp,
        OpExpression(_, _),
        lambda _, args: itertools.chain(result, map(inner, args)),
        AccessExpression(_, _),
        lambda _, args: itertools.chain(result, map(inner, args)),
        RefExpression(_),
        lambda var: [var],
        _,
        [],
    )

  return inner(exp, [])


def expression_to_isl(exp: Expression,
                      vars: List[VarID],
                      params: List[VarID] = [],
                      ctx: islpy.Context = islpy.DEFAULT_CONTEXT) -> islpy.Aff:
  """Cast expression to ISL's affine expression.

  Assumes `exp` is an affine expression, cast it to isl representation.
  """
  with tmp_var_allocator(ctx) as tmp_var_alloc:
    param_ids = [islpy.Id.alloc(ctx, name, None) for name in params]
    var_ids = tmp_var_alloc(len(vars))

  space = islpy.Space.create_from_names(ctx,
                                        set=list(map(str, var_ids)),
                                        params=list(map(str, param_ids)))

  vars_map = {
      name: islpy.Aff.zero_on_domain(space).set_coefficients_by_name(
          {var_id.get_name(): 1})
      for name, var_id in zip(itertools.chain(params, vars),
                              itertools.chain(param_ids, var_ids))
  }

  def handle_affine_expression(self: OpExpression) -> islpy.Aff:
    unary_ops = {"+": lambda x: x, "-": islpy.Aff.neg}
    if self.op in unary_ops and len(self.args) == 1:
      e = expression_to_isl_impl(self.args[0])
      return unary_ops[self.op](e)
    bin_ops = {
        "+": islpy.Aff.add,
        "-": islpy.Aff.sub,
        "*": islpy.Aff.mul,
        "/": islpy.Aff.div
    }
    if self.op in bin_ops and len(self.args) == 2:
      e1 = expression_to_isl_impl(self.args[0])
      e2 = expression_to_isl_impl(self.args[1])
      return bin_ops[self.op](e1, e2)
    raise TypeError("Cannot cast to affine expression.")

  def handle_const_expression(const_expr: ConstExpression):
    return islpy.Aff.val_on_domain_space(
        space, islpy.Val.int_from_si(ctx, const_expr.val))

  def raise_cannot_cast(exp: Expression):
    raise TypeError("Cannot cast {} to affine expression".format(exp))

  def expression_to_isl_impl(exp: Expression) -> islpy.Aff:
    return match(exp,                              \
      OpExpression,     handle_affine_expression,  \
      ConstExpression,  handle_const_expression,   \
      RefExpression(_), lambda var: vars_map[var], \
      _,                raise_cannot_cast)

  return expression_to_isl_impl(exp)

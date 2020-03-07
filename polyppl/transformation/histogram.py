"""Histogram transformation."""

from typing import List

import enum
import copy

import islpy

import polyppl.ir as ir


class AffineExprChecker(ir.AffineExprWalker):

  def __init__(self, stmt: ir.Statement, ctx: islpy.Context,
               domain_space_names: List[ir.VarID],
               param_space_names: List[ir.VarID],
               affine_annotation: ir.AffineExpresionCollector.AnnotationMap,
               *args, **kwargs):
    self.stmt = stmt
    # reads is empty because we don't need to traverse Subscript specifically
    reads = {}
    ir.AffineExprWalker.__init__(self, ctx, domain_space_names,
                                 param_space_names, affine_annotation, reads,
                                 *args, **kwargs)

  def handle_identity_affine_expr(self):
    node = self.cur_node
    aff = ir.ast_to_aff(node, self.ctx, self.domain_space_names,
                        self.param_space_names)
    bijective_map = self.stmt.lhs_proj_map.reverse().apply_range(
        islpy.BasicMap.from_aff(aff))
    if not bijective_map.is_bijective():
      raise ValueError("Cannot histogram the chosen side of comparison")


def histogram(prog: ir.Program, lhs: ir.VarID, non_affine_idx: int,
              left_or_right: ir.Statement.NonAffineConstraintLeftOrRight):
  prog = copy.deepcopy(prog)
  stmt = [
      stmt for _, _, stmt in prog.iter_named_statements()
      if stmt.lhs_array_name == lhs
  ]
  if len(stmt) == 0:
    raise ValueError("Statement with LHS not found")
  elif len(stmt) > 1:
    raise ValueError(
        "Histogram on multiple statements with same LHS not implemented")
  stmt = stmt[0]
  # check that the compared expression in the referenced expression is feasible
  LeftOrRight = ir.Statement.NonAffineConstraintLeftOrRight
  ref_ast = stmt.non_affine_constraints[non_affine_idx].get(
      (LeftOrRight.left
       if left_or_right == LeftOrRight.right else LeftOrRight.right))
  affine_expr_collector = ir.AffineExpresionCollector(stmt.param_space_names,
                                                      stmt.domain_space_names,
                                                      ref_ast)
  AffineExprChecker(stmt,
                    prog.ctx,
                    stmt.domain_space_names,
                    prog.param_space_names,
                    affine_expr_collector.annotation,
                    node=ref_ast)
  # Done checking, set histogram
  stmt.set_histogramed(non_affine_idx, left_or_right)
  return prog

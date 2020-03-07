"""ISL AST to Python AST.

This module implements recursive code generation from ISL to Python.
"""

from typing import Union, List, Dict, Tuple, Optional

import copy
import collections
import ast

import astor
import islpy

import polyppl.ir as ir
import polyppl.schedule as schedule
import polyppl.isl_utils as isl_utils

HistogramLhsReplaceMap = Dict[ir.VarID, Tuple[ir.Statement, List[ast.AST]]]


def code_gen_exp(node: islpy.AstExpr) -> ast.AST:
  # TODO(camyang) fix this laziness
  # this should not work for certain op type
  c_str = node.to_C_str().replace("&&", "and").replace("||",
                                                       "or").replace("/", "//")
  expr: ast.Expression = ast.parse(c_str, mode="eval")
  return expr.body


CodeGenRetType = Union[ast.AST, List[ast.AST]]


def code_gen_node(
    prog: ir.Program, node: islpy.AstNode,
    histogram_lhs_replace_map: HistogramLhsReplaceMap) -> CodeGenRetType:
  node_type = node.get_type()
  if node_type == islpy.ast_node_type.block:
    return code_gen_block_node(prog, node, histogram_lhs_replace_map)
  elif node_type == islpy.ast_node_type.for_:
    return code_gen_for_node(prog, node, histogram_lhs_replace_map)
  elif node_type == islpy.ast_node_type.if_:
    return code_gen_if_node(prog, node, histogram_lhs_replace_map)
  elif node_type == islpy.ast_node_type.user:
    return code_gen_user_node(prog, node, histogram_lhs_replace_map)
  else:
    raise ValueError("Codegen encountered unsupported node type")


def code_gen_block_node(
    prog: ir.Program, node: islpy.AstNode,
    histogram_lhs_replace_map: HistogramLhsReplaceMap) -> CodeGenRetType:
  ret = []
  block_inner_list = node.block_get_children()
  for i in range(block_inner_list.n_ast_node()):
    child_node = block_inner_list.get_ast_node(i)
    child_ast = code_gen_node(prog, child_node, histogram_lhs_replace_map)
    ret += listify_ast(child_ast)
  if len(ret) == 1:
    ret = ret[0]
  return ret


def listify_ast(ast: Union[List[ast.AST], ast.AST]) -> List[ast.AST]:
  if isinstance(ast, list):
    return ast
  else:
    return [ast]


def code_gen_for_node(prog: ir.Program,
                      node: islpy.AstNode,
                      histogram_lhs_replace_map: HistogramLhsReplaceMap,
                      prefer_generate_for=True) -> CodeGenRetType:
  """Generate ast for a loop node.

  This routine attempts to generate a for-range loop whenever possible (which
  is the case most of the time), and resort to a generic while loop if necessary

  Args:
    - prog: input program.
    - node: a islpy.AstNode to perform codegen.
    - histogram_lhs_replace_map: replacement map for handling of Histogram.
    - prefer_generate_for: only generate while loop if False.

  Returns:
    CodeGenRetType
  """
  iterator_id = node.for_get_iterator().get_id().get_name()
  init_exp = node.for_get_init()
  cond_exp = node.for_get_cond()
  inc_exp = node.for_get_inc()
  body_node = node.for_get_body()

  body_ast = code_gen_node(prog, body_node, histogram_lhs_replace_map)
  loop_body_ast = listify_ast(body_ast)

  generate_for = prefer_generate_for
  valid_for_cond_op_types = {
      islpy.ast_expr_op_type.ge, islpy.ast_expr_op_type.gt,
      islpy.ast_expr_op_type.le, islpy.ast_expr_op_type.lt
  }
  if (cond_exp.get_type() == islpy.ast_expr_type.op and
      cond_exp.get_op_type() in valid_for_cond_op_types and
      cond_exp.op_get_n_arg() == 2):
    left = cond_exp.op_get_arg(0)
    right = cond_exp.op_get_arg(1)
    if left == node.for_get_iterator():
      potential_cond_exp = right
      var_on_side = "left"
    elif right == node.for_get_iterator():
      potential_cond_exp = left
      var_on_side = "right"
    else:
      generate_for = False
    if generate_for:
      cond_ast = code_gen_exp(potential_cond_exp)
      cond_exp_fvs = set(ir.collect_free_vars(cond_ast))
      generate_for = iterator_id not in cond_exp_fvs
      if not generate_for:
        cond_ast = code_gen_exp(cond_exp)
  else:
    generate_for = False

  init_ast = code_gen_exp(init_exp)
  inc_ast = code_gen_exp(inc_exp)

  if generate_for:
    inc_exp_fvs = set(ir.collect_free_vars(inc_ast))
    generate_for = iterator_id not in inc_exp_fvs

  if generate_for:
    # Generate a for-range loop
    cond_ast_eq_adjust_map = {
        ("left", islpy.ast_expr_op_type.ge): -1,
        ("right", islpy.ast_expr_op_type.ge): 1,
        ("left", islpy.ast_expr_op_type.le): 1,
        ("right", islpy.ast_expr_op_type.ge): -1,
    }
    adjust_map_query = (var_on_side, cond_exp.get_op_type())
    if adjust_map_query in cond_ast_eq_adjust_map:
      # If cond op is <= or >=, adjust the +/-1 boundary for `range` call
      adjust = cond_ast_eq_adjust_map[adjust_map_query]
      if adjust == 1:
        cond_ast = ast.BinOp(left=cond_ast, op=ast.Add(), right=ast.Num(n=1))
      else:
        cond_ast = ast.BinOp(left=cond_ast, op=ast.Sub(), right=ast.Num(n=1))
    return ast.For(target=ast.Name(id=iterator_id, ctx=ast.Store()),
                   iter=ast.Call(func=ast.Name(id="range"),
                                 args=[init_ast, cond_ast, inc_ast],
                                 keywords=[]),
                   body=loop_body_ast,
                   orelse=[])
  else:
    # Generate a generic while loop
    cond_ast = code_gen_exp(cond_exp)

    init_ast = ast.Assign(targets=[ast.Name(id=iterator_id)], value=init_ast)
    inc_ast = ast.AugAssign(target=ast.Name(id=iterator_id),
                            op=ast.Add(),
                            value=inc_ast)
    loop_body_ast.append(inc_ast)
    return [init_ast, ast.While(test=cond_ast, body=loop_body_ast, orelse=[])]


def code_gen_if_node(
    prog: ir.Program, node: islpy.AstNode,
    histogram_lhs_replace_map: HistogramLhsReplaceMap) -> CodeGenRetType:
  """Generate ast for a condition node."""
  cond_exp = node.if_get_cond()
  cond_ast = code_gen_exp(cond_exp)

  then_node = node.if_get_then()
  then_ast = listify_ast(
      code_gen_node(prog, then_node, histogram_lhs_replace_map))

  if node.if_has_else():
    else_node = node.if_get_else()
    else_ast = listify_ast(
        code_gen_node(prog, else_node, histogram_lhs_replace_map))
  else:
    else_ast = []

  return ast.If(test=cond_ast, body=then_ast, orelse=else_ast)


class AffineExprReplacer(ir.AffineExprWalker):

  def __init__(self, decl_stmt: ir.Statement, replacement_asts: List[ast.AST],
               ctx: islpy.Context, param_space_names: List[ir.VarID],
               affine_annotation: ir.AffineExpresionCollector.AnnotationMap,
               *args, **kwargs):
    self.decl_stmt = decl_stmt
    domain_space_names = ir.tmp_vars(num=len(replacement_asts))
    self.replacement_map = {
        n: ast for n, ast in zip(domain_space_names, replacement_asts)
    }
    # reads is empty because we don't need to traverse Subscript specifically
    reads = {}
    ir.AffineExprWalker.__init__(self, ctx, domain_space_names,
                                 param_space_names, affine_annotation, reads,
                                 *args, **kwargs)

  def handle_identity_affine_expr(self):
    node = self.cur_node
    aff = ir.ast_to_aff(node, self.ctx, self.decl_stmt.domain_space_names,
                        self.param_space_names)
    bijective_map = self.decl_stmt.lhs_proj_map.reverse().apply_range(
        islpy.BasicMap.from_aff(aff))
    try:
      multi_aff = isl_utils.bijective_basic_map_to_multi_aff(bijective_map)
    except ValueError:
      raise ValueError("Incorrect histogram, the reference equality "
                       "is not expressible under referenced context")
    affine_ast = ir.multi_aff_to_ast(multi_aff, self.domain_space_names)[0]
    affine_ast = ir.ast_replace_free_vars(ast.Expression(body=affine_ast),
                                          self.replacement_map).body
    self.replace(affine_ast)


def replace_lhs_by_histogramed_access(
    array_ref_name: ir.VarID, prog: ir.Program, stmt: ir.Statement,
    histogram_lhs_replace_map: HistogramLhsReplaceMap,
    replacement_asts: List[ast.AST]) -> Optional[ast.AST]:
  """Replace histogram's reference side by the correct expression in context."""
  if array_ref_name in histogram_lhs_replace_map:
    decl_stmt, histogram_access_asts = histogram_lhs_replace_map[array_ref_name]
    histogram_index_asts = []
    for histogram_access_ast in histogram_access_asts:
      node = copy.deepcopy(ast.Expression(body=histogram_access_ast))
      affine_annotation = ir.AffineExpresionCollector(
          decl_stmt.param_space_names, decl_stmt.domain_space_names,
          node).annotation
      AffineExprReplacer(decl_stmt,
                         replacement_asts,
                         prog.ctx,
                         prog.param_space_names,
                         affine_annotation,
                         node=node)
      histogram_index_asts.append(node)
    if len(histogram_index_asts) == 0:
      return
    elif len(histogram_index_asts) == 1:
      return ast.Subscript(ast.Name(id=array_ref_name, ctx=ast.Load()),
                           slice=ast.Index(histogram_index_asts[0]))
    else:
      return ast.Subscript(ast.Name(id=array_ref_name, ctx=ast.Load()),
                           slice=ast.Index(
                               ast.Tuple(elts=histogram_index_asts)))


def code_gen_user_node(
    prog: ir.Program, node: islpy.AstNode,
    histogram_lhs_replace_map: HistogramLhsReplaceMap) -> CodeGenRetType:
  """Generate ast for a user node."""
  user_exp_node = node.user_get_expr()
  if (user_exp_node.get_type() != islpy.ast_expr_type.op or
      user_exp_node.get_op_type() != islpy.ast_expr_op_type.call):
    raise ValueError("Unrecognized user node")
  nargs = user_exp_node.op_get_n_arg()
  target = user_exp_node.op_get_arg(0)
  if target.get_type() != islpy.ast_expr_type.id:
    raise ValueError("Unrecognized user node")

  stmt_id_name = target.get_id().get_name()
  stmt_id = int(stmt_id_name[1:])
  stmt = prog.get_statement_by_id(stmt_id)

  if nargs != len(stmt.domain_space_names) + 1:
    raise ValueError("User node narg does not match domain space")

  replace_map = collections.OrderedDict()
  for i, name in enumerate(stmt.domain_space_names):
    arg_exp = user_exp_node.op_get_arg(i + 1)
    arg_ast = code_gen_exp(arg_exp)
    replace_map[name] = arg_ast

  non_aff_constraints_indices = set(range(len(stmt.non_affine_constraints)))
  non_histogramed_indices = non_aff_constraints_indices - {
      i for i, _ in stmt.histograms
  }

  class HistogramArrayRefRewriter(ir.AffineExprWalker):

    def handle_subscript_affine_expr(self):
      read = self.cur_node
      lhs_array_name = read.value.id
      if isinstance(read.slice.value, ast.Tuple):
        replacement_asts = read.slice.value.elts
      else:
        replacement_asts = [read.slice.value]
      replace_with = replace_lhs_by_histogramed_access(
          lhs_array_name, prog, stmt, histogram_lhs_replace_map,
          replacement_asts)
      if replace_with is not None:
        self.replace(ast.Subscript(value=replace_with, slice=read.slice))

  declared_lhs_symbols = [
      stmt.lhs_array_name for stmt in prog.statements.values()
  ]

  def replace_histogram_expr(node):
    affine_annotation = ir.AffineExpresionCollector(stmt.param_space_names,
                                                    stmt.domain_space_names,
                                                    node).annotation
    reads = schedule.ASTCollectRead(node, declared_lhs_symbols).reads
    HistogramArrayRefRewriter(prog.ctx, stmt.domain_space_names,
                              stmt.param_space_names, affine_annotation, reads,
                              node)

  lhs_index_ast_list = ir.multi_aff_to_ast(stmt.lhs_proj,
                                           stmt.domain_space_names)

  if len(lhs_index_ast_list) == 1:
    lhs_index_ast = lhs_index_ast_list[0]
  else:
    lhs_index_ast = ast.Tuple(elts=lhs_index_ast_list)
  lhs_index_ast = ast.Expression(body=lhs_index_ast)
  lhs_index_ast = ir.ast_replace_free_vars(lhs_index_ast, replace_map).body

  histogram_index_asts = []
  for histogram_idx, left_or_right in stmt.histograms:
    histogram = stmt.non_affine_constraints[histogram_idx]
    histogram_index_ast = ast.Expression(body=histogram.get(left_or_right))
    histogram_index_ast = ir.ast_replace_free_vars(histogram_index_ast,
                                                   replace_map)
    import pdb
    pdb.set_trace()
    replace_histogram_expr(histogram_index_ast)
    histogram_index_asts.append(histogram_index_ast.body)

  array_ast = ast.Name(id=stmt.lhs_array_name)
  if len(histogram_index_asts) > 0:
    if len(histogram_index_asts) == 1:
      histogram_index_ast = histogram_index_asts[0]
    else:
      histogram_index_ast = ast.Tuple(elts=histogram_index_asts)
    array_ast = ast.Subscript(value=array_ast, slice=histogram_index_ast)

  subscript_ast = ast.Subscript(value=array_ast,
                                slice=ast.Index(value=lhs_index_ast))

  rhs_ast = ir.ast_replace_free_vars(stmt.rhs, replace_map)
  replace_histogram_expr(rhs_ast)
  rhs_ast = rhs_ast.body

  if stmt.is_reduction:
    op_map = {"+": ast.Add, "*": ast.Mult}
    if stmt.op in op_map:
      assign_ast = ast.AugAssign(target=subscript_ast,
                                 op=op_map[stmt.op](),
                                 value=rhs_ast)
    else:
      assign_ast = ast.Assign(targets=[subscript_ast],
                              value=ast.Call(func=ast.Name(id=stmt.op),
                                             args=[subscript_ast, rhs_ast],
                                             keywords=[]))
  else:
    assign_ast = ast.Assign(targets=[subscript_ast], value=rhs_ast)

  # Generate guard for any non-histogramed constraints
  guard_compares = []
  for non_histogram_idx in non_histogramed_indices:
    non_histogram = stmt.non_affine_constraints[non_histogram_idx]
    left = ir.ast_replace_free_vars(non_histogram.left, replace_map)
    right = ir.ast_replace_free_vars(non_histogram.right, replace_map)
    guard_compares.append(
        ast.Compare(left=left, ops=[ast.Eq()], comparators=[right]))

  if len(guard_compares) > 1:
    guard_test = ast.BoolOp(op=ast.And(), values=guard_compares)
  elif len(guard_compares) == 1:
    guard_test = guard_compares[0]

  if len(guard_compares) > 0:
    guard_test = ast.Expression(body=guard_test)
    replace_histogram_expr(guard_test)
    guard_test = guard_test.body  # pylint: disable=no-member
    assign_ast = ast.If(test=guard_test, body=[assign_ast], orelse=[])

  return assign_ast


def isl_ast_code_gen(prog: ir.Program, isl_ast: islpy.AstNode) -> ast.AST:
  histogram_lhs_replace_map: HistogramLhsReplaceMap = {}
  LeftOrRight = ir.Statement.NonAffineConstraintLeftOrRight
  for _, _, stmt in prog.iter_named_statements():
    histogram_ref_asts = []
    for histogram_idx, left_or_right in stmt.histograms:
      left_or_right = (LeftOrRight.left if left_or_right == LeftOrRight.right
                       else LeftOrRight.right)
      histogram = stmt.non_affine_constraints[histogram_idx]
      histogram_ref_asts.append(histogram.get(left_or_right))
    if len(histogram_ref_asts) > 0:
      histogram_lhs_replace_map[stmt.lhs_array_name] = (stmt,
                                                        histogram_ref_asts)

  ret_ast = code_gen_node(prog, isl_ast, histogram_lhs_replace_map)
  ret_ast = ast.Module(body=listify_ast(ret_ast))
  return ret_ast


def debug_ast_node_to_str(isl_ast: islpy.AstNode) -> str:
  printer = islpy.Printer.to_str(isl_ast.get_ctx())
  printer = printer.set_output_format(islpy.format.C)
  printer.flush()
  printer.print_ast_node(isl_ast)
  return printer.get_str()


def prog_to_ast(prog: ir.Program) -> ast.AST:
  new_prog, barrier_map = schedule.inject_reduction_barrier_statements(prog)
  sched = schedule.schedule_program(new_prog)
  isl_ast = schedule.schedule_isl_ast_gen(new_prog,
                                          sched,
                                          barrier_map=barrier_map)
  cgen_ast = isl_ast_code_gen(prog, isl_ast)
  return cgen_ast


def prog_str_to_ast(prog_str: str) -> ast.AST:
  prog = ir.Program.read_from_string(prog_str)
  return prog_to_ast(prog)

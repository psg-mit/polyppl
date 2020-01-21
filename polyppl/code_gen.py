import ast
import astor

import islpy

from polyppl.ir import Program, ast_replace_free_vars, multi_aff_to_ast
from polyppl.isl_patch import isl_ast_node_block_get_children


def code_gen_node(prog: Program, node: islpy.AstNode) -> ast.AST:
  node_type = node.get_type()
  if node_type == islpy.ast_node_type.block:
    return code_gen_block_node(prog, node)
  elif node_type == islpy.ast_node_type.for_:
    return code_gen_for_node(prog, node)
  elif node_type == islpy.ast_node_type.if_:
    return code_gen_if_node(prog, node)
  elif node_type == islpy.ast_node_type.user:
    return code_gen_user_node(prog, node)
  else:
    raise ValueError("Codegen encountered unsupported node type")


def code_gen_exp(node: islpy.AstExpr) -> ast.AST:
  c_str = node.to_C_str().replace("&&", "and").replace("||", "or")
  return ast.parse(c_str, mode="eval").body


def code_gen_block_node(prog: Program, node: islpy.AstNode) -> ast.AST:
  ret = []
  for child_node in isl_ast_node_block_get_children(node):
    child_ast = code_gen_node(prog, child_node)
    if isinstance(child_ast, list):
      ret += child_ast
    else:
      ret.append(child_ast)
  if len(ret) == 1:
    ret = ret[0]
  return ret


def code_gen_for_node(prog: Program, node: islpy.AstNode) -> ast.AST:
  iterator_id = node.for_get_iterator().get_id().get_name()
  init_exp = node.for_get_init()
  cond_exp = node.for_get_cond()
  inc_exp = node.for_get_inc()
  body_node = node.for_get_body()

  body_ast = code_gen_node(prog, body_node)
  while_loop_body_ast = []
  if type(body_ast) is list:
    while_loop_body_ast = body_ast
  else:
    while_loop_body_ast = [body_ast]

  init_ast = ast.Assign(targets=[ast.Name(id=iterator_id)],
                        value=code_gen_exp(init_exp))
  cond_ast = code_gen_exp(cond_exp)
  inc_ast = ast.AugAssign(target=ast.Name(id=iterator_id),
                          op=ast.Add(),
                          value=code_gen_exp(inc_exp))
  while_loop_body_ast.append(inc_ast)
  return [
      init_ast,
      ast.While(test=cond_ast, body=while_loop_body_ast, orelse=[])
  ]


def code_gen_if_node(prog: Program, node: islpy.AstNode) -> ast.AST:
  cond_exp = node.if_get_cond()
  cond_ast = code_gen_exp(cond_exp)

  then_node = node.if_get_then()
  then_ast = code_gen_node(prog, then_node)
  if not isinstance(then_ast, list):
    then_ast = [then_ast]

  if node.if_has_else():
    else_node = node.if_get_else()
    else_ast = code_gen_node(prog, else_node)
  else:
    else_ast = []
  if not isinstance(else_ast, list):
    else_ast = [else_ast]

  return ast.If(test=cond_ast, body=then_ast, orelse=else_ast)


def code_gen_user_node(prog: Program, node: islpy.AstNode) -> ast.AST:
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

  replace_map = {}
  for i, name in enumerate(stmt.domain_space_names):
    arg_exp = user_exp_node.op_get_arg(i + 1)
    arg_ast = ast.parse(arg_exp.to_C_str(), mode="eval").body
    replace_map[name] = arg_ast

  lhs_index_ast_list = multi_aff_to_ast(stmt.lhs_proj, stmt.domain_space_names)
  if len(lhs_index_ast_list) == 1:
    lhs_index_ast = lhs_index_ast_list[0]
  else:
    lhs_index_ast = ast.Tuple(elts=lhs_index_ast_list)
  lhs_index_ast = ast.Expression(body=lhs_index_ast)
  lhs_index_ast = ast_replace_free_vars(lhs_index_ast, replace_map).body

  rhs_ast = ast_replace_free_vars(stmt.rhs, replace_map).body

  subscript_ast = ast.Subscript(value=ast.Name(id=stmt.lhs_array_name),
                                slice=ast.Index(value=lhs_index_ast))
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
  return assign_ast


def isl_ast_code_gen(prog: Program, isl_ast: islpy.AstNode) -> ast.AST:
  ret_ast = code_gen_node(prog, isl_ast)
  ret_ast = ast.Module(body=ret_ast)
  return ret_ast


def debug_ast_node_to_str(isl_ast: islpy.AstNode) -> str:
  printer = islpy.Printer.to_str(isl_ast.get_ctx())
  printer = printer.set_output_format(islpy.format.C)
  printer.flush()
  printer.print_ast_node(isl_ast)
  return printer.get_str()

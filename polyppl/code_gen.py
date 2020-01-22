from typing import Union, List

import ast
import astor

import islpy

from polyppl.isl_patch import isl_ast_node_block_get_children
import polyppl.ir as ir
import polyppl.schedule as schedule


def code_gen_exp(node: islpy.AstExpr) -> ast.AST:
  # TODO(camyang) fix this lazziness
  # this should not work for certain op type
  c_str = node.to_C_str().replace("&&", "and").replace("||", "or")
  return ast.parse(c_str, mode="eval").body


def code_gen_node(prog: ir.Program, node: islpy.AstNode) -> ast.AST:
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


def code_gen_block_node(prog: ir.Program, node: islpy.AstNode) -> ast.AST:
  ret = []
  for child_node in isl_ast_node_block_get_children(node):
    child_ast = code_gen_node(prog, child_node)
    ret += listify_ast(child_ast)
  if len(ret) == 1:
    ret = ret[0]
  return ret


def listify_ast(ast: Union[List[ast.AST], ast.AST]) -> List[ast.AST]:
  if isinstance(ast, list):
    return ast
  else:
    return [ast]


def code_gen_for_node(prog: ir.Program, node: islpy.AstNode) -> ast.AST:

  iterator_id = node.for_get_iterator().get_id().get_name()
  init_exp = node.for_get_init()
  cond_exp = node.for_get_cond()
  inc_exp = node.for_get_inc()
  body_node = node.for_get_body()

  body_ast = code_gen_node(prog, body_node)
  loop_body_ast = listify_ast(body_ast)

  generate_for = True
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
    elif right == node.for_get_iterator():
      potential_cond_exp = left
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


def code_gen_if_node(prog: ir.Program, node: islpy.AstNode) -> ast.AST:
  cond_exp = node.if_get_cond()
  cond_ast = code_gen_exp(cond_exp)

  then_node = node.if_get_then()
  then_ast = listify_ast(code_gen_node(prog, then_node))

  if node.if_has_else():
    else_node = node.if_get_else()
    else_ast = listify_ast(code_gen_node(prog, else_node))
  else:
    else_ast = []

  return ast.If(test=cond_ast, body=then_ast, orelse=else_ast)


def code_gen_user_node(prog: ir.Program, node: islpy.AstNode) -> ast.AST:
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

  lhs_index_ast_list = ir.multi_aff_to_ast(stmt.lhs_proj,
                                           stmt.domain_space_names)
  if len(lhs_index_ast_list) == 1:
    lhs_index_ast = lhs_index_ast_list[0]
  else:
    lhs_index_ast = ast.Tuple(elts=lhs_index_ast_list)
  lhs_index_ast = ast.Expression(body=lhs_index_ast)
  lhs_index_ast = ir.ast_replace_free_vars(lhs_index_ast, replace_map).body

  rhs_ast = ir.ast_replace_free_vars(stmt.rhs, replace_map).body

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


def isl_ast_code_gen(prog: ir.Program, isl_ast: islpy.AstNode) -> ast.AST:
  ret_ast = code_gen_node(prog, isl_ast)
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

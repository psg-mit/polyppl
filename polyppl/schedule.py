"""Dependence analysis and Scheduling"""

from typing import List, Iterator, Dict, Tuple, Optional

import copy
import itertools

import ast

import ast_scope
import astor
import islpy

import polyppl.ir as ir


def collect_writes(prog: ir.Program) -> islpy.UnionMap:
  writes = islpy.UnionMap.empty(
      islpy.Space.create_from_names(prog.ctx,
                                    in_=[],
                                    out=[],
                                    params=prog.param_space_names))
  for stmt_id, stmt in prog.statements.items():
    stmt_id_name = "S{}".format(stmt_id)
    stmt_writes = stmt.lhs_proj_map.intersect_domain(
        stmt.domain).set_tuple_name(islpy.dim_type.in_,
                                    stmt_id_name).set_tuple_name(
                                        islpy.dim_type.out, stmt.lhs_array_name)
    writes = writes.union(stmt_writes)
  return writes


class ASTCollectRead(astor.TreeWalk):

  def __init__(self,
               node: ast.Expression,
               declared_lhs_symbols: List[ir.VarID],
               scope_info=None,
               *args,
               **kwargs):
    if scope_info is None:
      scope_info = ast_scope.annotate(node)
    self.scope_info = scope_info
    self.declared_lhs_symbols = set(declared_lhs_symbols)
    astor.TreeWalk.__init__(self, node=node, *args, **kwargs)

  def init_Subscript(self):
    self.reads = []

  def pre_Subscript(self):
    node = self.cur_node
    if isinstance(node.value, ast.Name):
      if isinstance(self.scope_info[node.value], ast_scope.scope.GlobalScope):
        if node.value.id in self.declared_lhs_symbols:
          slic = node.slice
          if not isinstance(slic, ast.Index):
            raise ValueError(
                "Advanced indexing for array reads within IR not implemented")
          self.reads.append(node)
    else:
      raise Warning(
          "Ignored array access {}: assume does not exist dependency on IR arrays"
          .format(node))


def collect_reads(prog: ir.Program) -> islpy.UnionMap:
  declared_lhs_symbols = [
      stmt.lhs_array_name for stmt in prog.statements.values()
  ]
  reads = islpy.UnionMap.empty(
      islpy.Space.create_from_names(prog.ctx,
                                    in_=[],
                                    out=[],
                                    params=prog.param_space_names))
  for _, stmt_id_name, stmt in prog.iter_named_statements():
    rhs_exprs = list(
        itertools.chain.from_iterable(
            [c.left, c.right]
            for c in stmt.non_affine_constraints)) + [stmt.rhs.body]
    expr = ast.Expression(body=ast.Tuple(elts=rhs_exprs))
    affine_expr_collector = ir.AffineExpresionCollector(stmt.param_space_names,
                                                        stmt.domain_space_names,
                                                        expr)
    read_asts = ASTCollectRead(expr, declared_lhs_symbols).reads
    for read_ast in read_asts:
      read_map = ir.read_ast_to_map(
          read_ast, prog.ctx, stmt.domain_space_names, stmt.param_space_names,
          affine_expr_collector.annotation).align_params(
              stmt.domain.get_space().params())
      read_map = read_map.intersect_domain(stmt.domain).set_tuple_name(
          islpy.dim_type.in_,
          stmt_id_name).set_tuple_name(islpy.dim_type.out, read_ast.value.id)
      reads = reads.union(read_map)
  return reads


def compute_dependencies(prog: ir.Program) -> islpy.UnionMap:
  reads = collect_reads(prog)
  writes = collect_writes(prog)
  return writes.apply_range(reads.reverse())


BarrierMap = Dict[ir.Program.StatementID, ir.Program.StatementID]


def inject_reduction_barrier_statements(
    prog: ir.Program) -> Tuple[ir.Program, BarrierMap]:
  """Injects reduction barriers into the program.

  Reduction barrier is effectively a dummy statement that prevents each
  reduction's left hand side being interleaved with some other statement.
  The injected statements' stmt_id can be accesd through the BarrierMap, which
  holds a map from old_reduction_id -> injected_reduction_id.
  """
  new_prog = copy.deepcopy(prog)
  barrier_map: BarrierMap = {}
  for stmt_id, _, stmt in prog.iter_named_statements():
    if stmt.is_reduction:
      intermediate_lhs_array_name = "_{}_".format(stmt.lhs_array_name)
      new_prog.get_statement_by_id(
          stmt_id).lhs_array_name = intermediate_lhs_array_name
      tvars = ir.tmp_vars(num=stmt.lhs_domain.n_dim())
      lhs_proj = islpy.MultiAff.identity_on_domain_space(
          stmt.lhs_domain.get_space())
      new_stmt = ir.Statement(
          stmt.lhs_domain, stmt.param_space_names, tvars, stmt.lhs_array_name,
          ast.parse("{}[{}]".format(intermediate_lhs_array_name,
                                    ",".join(tvars)),
                    mode="eval"), lhs_proj)
      new_stmt_id = new_prog.add_statement(new_stmt)
      barrier_map[stmt_id] = new_stmt_id
  return new_prog, barrier_map


def program_get_domain(prog: ir.Program) -> islpy.UnionSet:
  instance_set = islpy.UnionSet.empty(
      islpy.Space.create_from_names(prog.ctx,
                                    set=[],
                                    params=prog.param_space_names))
  for _, stmt_id_name, stmt in prog.iter_named_statements():
    instance_set = instance_set.union(stmt.domain.set_tuple_name(stmt_id_name))
  return instance_set


def schedule_program(prog: ir.Program) -> islpy.Schedule:
  deps = compute_dependencies(prog)
  instance_set = program_get_domain(prog)
  schedule_constraint = islpy.ScheduleConstraints.on_domain(instance_set)
  schedule_constraint = islpy.ScheduleConstraints.set_validity(
      schedule_constraint, deps)
  schedule_constraint = islpy.ScheduleConstraints.set_proximity(
      schedule_constraint, deps)
  schedule = islpy.ScheduleConstraints.compute_schedule(schedule_constraint)
  return schedule


def schedule_isl_ast_gen(
    prog: ir.Program,
    schedule: islpy.Schedule,
    barrier_map: Optional[BarrierMap] = None) -> islpy.AstNode:

  # param_context asserts that all parameters are positive
  param_space = islpy.Space.create_from_names(
      prog.ctx, set=[], params=prog.param_space_names).params()
  param_context = islpy.Set.universe(param_space)
  for param_name in param_space.get_var_names(islpy.dim_type.param):
    is_postive_constraint = islpy.Constraint.ineq_from_names(
        param_space, {
            1: -1,
            param_name: 1
        })
    param_context = param_context.add_constraint(is_postive_constraint)

  ast_build = islpy.AstBuild.from_context(param_context)

  schedule_map = schedule.get_map().intersect_domain(program_get_domain(prog))

  if barrier_map is not None:
    barrier_stmt_ids = set(barrier_map.values())
    to_remove_statements = {
        stmt_id_name
        for stmt_id, stmt_id_name, stmt in prog.iter_named_statements()
        if stmt_id in barrier_stmt_ids
    }
    schedule_map = schedule_map.remove_map_if(
        lambda m: m.get_tuple_name(islpy.dim_type.in_) in to_remove_statements)

  ast = ast_build.node_from_schedule_map(schedule_map)
  return ast

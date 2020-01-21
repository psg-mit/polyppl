"""AST."""

from __future__ import annotations

from typing import NewType, List, Tuple, Optional, Dict, Sequence, Union
from typing import Iterator

from dataclasses import dataclass

import os
import collections
import itertools
import enum
import operator
import contextlib
import ast
import symtable
import re
import copy
from functools import reduce

from ordered_set import OrderedSet

from pampy import match, _

from lark import Lark
import lark.exceptions

import islpy

import astor
import ast_scope

from polyppl.isl_utils import align_with_ids
from polyppl.isl_patch import isl_ast_node_block_get_children

VarID = NewType("VarID", str)
ArrayID = NewType("ArrayID", str)
OpID = NewType("OpID", str)

BasicSet = islpy.BasicSet
BasicMap = islpy.BasicMap
MultiAff = islpy.MultiAff
islpyError = islpy._isl.Error

################################################################################
#    BEGIN Expression
################################################################################


@contextlib.contextmanager
def tmp_var_allocator(ctx: Optional[islpy.Context] = None,
                      basename: Optional[str] = None):
  # TODO(camyang) better design here
  count = 0

  def tmp_var_allocator(num: int = 1) -> Union[List["VarID"], List[islpy.Id]]:
    ret = [VarID("_i{}".format(count + i)) for i in range(num)]
    if ctx is not None:
      ret = [islpy.Id.alloc(ctx, v, None) for v in ret]
    nonlocal count
    count += num
    return ret

  yield tmp_var_allocator


def tmp_vars(ctx: Optional[islpy.Context] = None,
             basename: Optional[str] = None,
             num: int = 1):
  with tmp_var_allocator(ctx, basename) as tmp_var_alloc:
    return tmp_var_alloc(num)


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
  def from_isl_aff_exp(aff: islpy.Aff) -> AffineExpression:
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


################################################################################
#    BEGIN ast Expression
################################################################################


def collect_free_vars(node: ast.AST):
  """Collects the free variables from node.

  Note that this function uses symtable,
  which requires potentially re-parsing from Python source.
  """
  src = astor.to_source(node)
  symbol_table = symtable.symtable(src, "top", "exec")

  def collect_from_tab(tab: symtable.SymbolTable):
    ret = []
    for symb in tab.get_symbols():
      # For some reason, symb.is_free doesn't seem to work...
      # But the test below does the trick
      if (symb.is_referenced() and symb.is_global() and
          not symb.is_declared_global()):
        ret.append(symb.get_name())

    for subtab in tab.get_children():
      ret += collect_from_tab(subtab)
    return ret

  return collect_from_tab(symbol_table)


class NameReplacer(astor.TreeWalk):
  """Replaces global names in a python expression. """

  def __init__(self,
               replace_map: Dict[VarID, ast.Expression],
               node: ast.Expression,
               scope_info=None,
               *args,
               **kwargs):
    self.replace_map = replace_map
    if scope_info is None:
      scope_info = ast_scope.annotate(node)
    self.scope_info = scope_info
    astor.TreeWalk.__init__(self, node=node, *args, **kwargs)

  def post_Name(self):
    node = self.cur_node
    if isinstance(self.scope_info[node], ast_scope.scope.GlobalScope):
      if node.id in self.replace_map:
        new_node = self.replace_map[node.id]
        self.replace(new_node)


def ast_replace_free_vars(node: ast.Expression,
                          replacement_map: Dict[VarID, ast.Expression]):
  """Replaces global free variables in a python ast expression.

  Args:
    node: a python expression parsed from ast.parse(src, mode="eval")
    replacement_map: dict representing the mapping of replacement.

  Returns:
    a new copy of node where all free variables have been replaced according to
    `replacement_map`.
  """
  node = copy.deepcopy(node)
  NameReplacer(replacement_map, node)  # Modifies node in-place
  return node


################################################################################
#    BEGIN Statement
################################################################################


def aff_to_ast(aff: islpy.Aff, domain_space_names: List[VarID]) -> ast.AST:
  aff = align_with_ids(aff, domain_space_names)
  coeffs = aff.get_coefficients_by_name(islpy.dim_type.in_)
  terms = []
  for var, coeff in coeffs.items():
    if var == 1:
      coeff = coeff.floor().to_python()
      if coeff == 0:
        continue
      term = ast.Num(n=coeff)
    else:
      numerator = coeff.get_num_si()
      if numerator == 1:
        term = ast.Name(id=var, ctx=ast.Load())
      elif numerator == 0:
        continue
      else:
        term = ast.BinOp(left=ast.Num(n=numerator),
                         op=ast.Mult(),
                         right=ast.Name(id=var, ctx=ast.Load()))
      try:
        denom = coeff.get_den_val().to_python()
        if denom != 1:
          term = ast.BinOp(left=term, op=ast.FloorDiv(), right=ast.Num(denom))
      except:
        raise ValueError(
            "Failed to cast multiaff due to denomerator not a python value")
    terms.append(term)
  if len(terms) > 0:
    aff_ast = reduce(
        lambda left, right: ast.BinOp(left=left, op=ast.Add(), right=right),
        terms[1:], terms[0])
  else:
    aff_ast = ast.Num(n=0)
  return aff_ast


def multi_aff_to_ast(multiaff: islpy.MultiAff,
                     domain_space_names: List[VarID]) -> List[ast.AST]:
  """Converts islpy.MultiAff into a python ast."""
  multiaff = align_with_ids(multiaff, domain_space_names)
  aff_asts = []
  for i in range(multiaff.dim(islpy.dim_type.out)):
    aff = multiaff.get_at(i)
    aff_ast = aff_to_ast(aff, domain_space_names)
    aff_asts.append(aff_ast)
  return aff_asts


class Statement(object):

  class NonAffineConstraint(object):

    def __init__(self, left, right):
      self.left = left
      self.right = right

    def __eq__(self, other):
      if isinstance(other, Statement.NonAffineConstraint):
        return {self.left, self.right} == {other.left, other.right}
      else:
        return False

  ReductionOpId = NewType("ReductionOpId", str)

  def __init__(self,
               domain: BasicSet,
               param_space_names: List[VarID],
               domain_space_names: List[VarID],
               lhs_array_name: ArrayID,
               rhs: Expression,
               lhs_proj: MultiAff,
               op: Optional[ReductionOpId] = None,
               non_affine_constraints: List[NonAffineConstraint] = []):
    self.domain = domain
    self.param_space_names = param_space_names
    self.domain_space_names = domain_space_names
    self.lhs_array_name = lhs_array_name
    self.lhs_proj = lhs_proj
    self.op = op
    self.rhs = rhs
    self.non_affine_constraints = non_affine_constraints

  @property
  def is_reduction(self):
    return self.op is not None

  @property
  def lhs_domain(self):
    return self.domain.apply(self.lhs_proj_map)

  @property
  def lhs_proj_map(self) -> BasicMap:
    return BasicMap.from_multi_aff(self.lhs_proj)

  def _set_parent_program(self, prog: Program):
    self._prog = prog

  @property
  def parent_program(self):
    return self._prog

  @property
  def belongs_to_program(self) -> bool:
    return self._prog is not None

  RE_TUPLE = r"\[[^\]]+\]"
  ARROW = r"\s*->\s*"
  RE_LHS_PROJ = \
    fr"({RE_TUPLE}){ARROW}{{\s*{RE_TUPLE}{ARROW}(?P<aff_list>{RE_TUPLE})\s*}}"
  RE_DOMAIN = fr"{RE_TUPLE}{ARROW}(?P<polyhedron>{{[^}}]+}})"

  def __repr__(self):
    aff_list_ast = multi_aff_to_ast(self.lhs_proj, self.domain_space_names)
    aff_list_str = ",".join(
        astor.to_source(aff_ast)[:-1] for aff_ast in aff_list_ast)
    domain_str = align_with_ids(self.domain, self.domain_space_names).to_str()
    polyhedron_str = re.match(self.RE_DOMAIN, domain_str)
    polyhedron = polyhedron_str.group("polyhedron")
    rhs_code = astor.to_source(self.rhs)
    rhs_code = rhs_code[:-1]  # removes training newline
    return ("{lhs_array_name}[{aff_list}] "
            "{op}= {expression}\t# {polyhedron};").format(
                lhs_array_name=self.lhs_array_name,
                aff_list=aff_list_str,
                op=self.op if self.op else "",
                expression=rhs_code,
                polyhedron=polyhedron)

  def __eq__(self, other):
    if not isinstance(other, Statement):
      return False
    return (self.domain == other.domain and
            self.param_space_names == other.param_space_names and
            self.domain_space_names == other.domain_space_names and
            self.lhs_proj == other.lhs_proj and
            self.lhs_array_name == other.lhs_array_name and
            self.op == other.op and
            self.non_affine_constraints == other.non_affine_constraints and
            self.rhs == other.rhs)


class Program(object):

  StatementID = NewType("StatementID", int)

  def __init__(self, ctx: islpy.Context):
    self.ctx = ctx
    self.param_space_names = OrderedSet()
    self.statements = collections.OrderedDict()
    self._unique_id_counter = 0

  def add_params(self, param_space_names: Sequence[VarID]):
    for psn in param_space_names:
      self.param_space_names.add(psn)

  def add_statement(self, stmt: Statement):
    self.add_params(stmt.param_space_names)
    stmt_id = self._unique_id_counter
    self.statements[stmt_id] = stmt
    self._unique_id_counter += 1
    stmt._set_parent_program(self)
    return stmt_id

  def get_statement_by_id(self, statement_id):
    return self.statements[statement_id]

  def pop_statement(self):
    return self.statements.popitem(last=True)

  def remove_statement(self, statement_id):
    self.statements.pop(statement_id)

  class ProgramParseError(ValueError):
    pass

  @staticmethod
  def read_from_string(src: str, ctx: islpy.Context = islpy.DEFAULT_CONTEXT):

    def get_text_from_node(ast_node) -> str:
      return src[ast_node.meta.start_pos:ast_node.meta.end_pos]

    def safe_find_data(node, data: str):
      try:
        return next(node.find_data(data))
      except StopIteration:
        raise Program.ProgramParseError("Cannot find {} in {}".format(
            data, node))

    grammar_path = os.path.join(os.path.dirname(__file__), 'grammar.lark')
    with open(grammar_path, "r") as grammar:
      parser = Lark(grammar, propagate_positions=True)

    try:
      ir_ast = parser.parse(src)
    except lark.exceptions.LarkError:
      raise Program.ProgramParseError("Cannot parse")

    params = [str(param) for param in safe_find_data(ir_ast, "params").children]
    program_ast = next(ir_ast.find_data("program"))
    statements_ast = program_ast.children

    prog = Program(ctx)
    prog.add_params(params)

    for stmt_ast in statements_ast:
      lhs_array_name = str(safe_find_data(stmt_ast, "lhs_array").children[0])
      param_space_names = params
      domain_str = "[{0}] -> {{ {1} }}".format(
          ",".join(param_space_names),
          get_text_from_node(safe_find_data(stmt_ast, "polyhedron")))
      try:
        domain = islpy.BasicSet.read_from_str(ctx, domain_str)
      except islpyError:
        raise Program.ProgramParseError(
            "Cannot parse domain {}".format(domain_str))

      domain_space_names = domain.get_var_names(islpy.dim_type.set)

      # Parse rhs expression into python ast
      rhs = get_text_from_node(safe_find_data(stmt_ast, "expression"))
      rhs = rhs.lstrip()  # Remove leading whitespaces
      rhs = ast.parse(rhs, mode="eval")

      lhs_proj = "[{0}] -> {{ [{1}] -> [{2}] }}".format(
          ",".join(param_space_names), ",".join(domain_space_names),
          get_text_from_node(safe_find_data(stmt_ast,
                                            "aff_list")).replace("//", "/"))
      try:
        lhs_proj = islpy.MultiAff.read_from_str(ctx, lhs_proj)
      except islpyError:
        raise Program.ProgramParseError("Invalid lhs_proj")

      try:
        op = next(stmt_ast.find_data("op"))
        op = str(op.children[0])
      except StopIteration:
        op = None
        if not islpy.BasicMap.from_multi_aff(lhs_proj).is_bijective():
          raise Program.ProgramParseError(
              "lhs_proj is not bijective while statement is not a reduction")

      prog.add_statement(
          Statement(domain,
                    param_space_names,
                    domain_space_names,
                    lhs_array_name,
                    rhs,
                    lhs_proj,
                    op=op))
    return prog

  def __repr__(self):
    s = ""
    s += " ".join(self.param_space_names) + "\n"
    for i, stmt in enumerate(self.statements.values()):
      s += repr(stmt)
      if i != len(self.statements) - 1:
        s += "\n"
    return s

  def __eq__(self, other):
    """Checks for plain equality.

    That is, all parameters and all statements have to be exactly the same for
    two programs to be equal.
    """
    if not isinstance(other, Program):
      return False
    if self.param_space_names != other.param_space_names:
      return False
    if len(self.statements) != len(other.statements):
      return False
    for stmt1, stmt2 in zip(self.statements, other.statements):
      if stmt1 != stmt2:
        return False
    return True


################################################################################
# Dependence analysis and Scheduling
################################################################################


def collect_writes(prog: Program) -> islpy.UnionMap:
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
               declared_lhs_symbols: List[VarID],
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


def iter_named_statements(prog: Program) -> Iterator[str]:
  for stmt_id, stmt in prog.statements.items():
    yield stmt_id, "S{}".format(stmt_id), stmt


def collect_reads(prog: Program) -> islpy.UnionMap:
  declared_lhs_symbols = [
      stmt.lhs_array_name for stmt in prog.statements.values()
  ]
  reads = islpy.UnionMap.empty(
      islpy.Space.create_from_names(prog.ctx,
                                    in_=[],
                                    out=[],
                                    params=prog.param_space_names))
  for _, stmt_id_name, stmt in iter_named_statements(prog):
    read_asts = ASTCollectRead(stmt.rhs, declared_lhs_symbols).reads
    for read_ast in read_asts:
      slic = read_ast.slice
      if isinstance(slic.value, ast.Tuple):
        # Multiple argument indexing
        if len(slic.value.elts) == 0:
          raise ValueError("Indexed defined array with empty "
                           "tuple instead of affine expression")
        if len(slic.value.elts) == 1:
          target_str = astor.to_source(slic.value.elts[0])[:-1]
        else:
          target_str = astor.to_source(slic)[1:-2]
      else:
        # Single argument indexing
        target_str = astor.to_source(slic)[:-1]
      read_map_str = "[{}] -> {{ [{}] -> [{}] : }}".format(
          ",".join(stmt.param_space_names), ",".join(stmt.domain_space_names),
          target_str)
      read_map = islpy.BasicMap.read_from_str(prog.ctx, read_map_str)
      read_map = read_map.intersect_domain(stmt.domain).set_tuple_name(
          islpy.dim_type.in_,
          stmt_id_name).set_tuple_name(islpy.dim_type.out, read_ast.value.id)
      reads = reads.union(read_map)
  return reads


def compute_dependencies(prog: Program) -> islpy.UnionMap:
  reads = collect_reads(prog)
  writes = collect_writes(prog)
  return writes.apply_range(reads.reverse())


BarrierMap = Dict[Program.StatementID, Program.StatementID]


def inject_reduction_barrier_statements(
    prog: Program) -> Tuple[Program, BarrierMap]:
  new_prog = copy.deepcopy(prog)
  barrier_map: BarrierMap = {}
  for stmt_id, _, stmt in iter_named_statements(prog):
    if stmt.is_reduction:
      intermediate_lhs_array_name = "_{}_".format(stmt.lhs_array_name)
      new_prog.get_statement_by_id(
          stmt_id).lhs_array_name = intermediate_lhs_array_name
      tvars = tmp_vars(num=stmt.lhs_domain.n_dim())
      lhs_proj = islpy.MultiAff.identity_on_domain_space(
          stmt.lhs_domain.get_space())
      new_stmt = Statement(
          stmt.lhs_domain, stmt.param_space_names, tvars, stmt.lhs_array_name,
          ast.parse("{}[{}]".format(intermediate_lhs_array_name,
                                    ",".join(tvars)),
                    mode="eval"), lhs_proj)
      new_stmt_id = new_prog.add_statement(new_stmt)
      barrier_map[stmt_id] = new_stmt_id
  return new_prog, barrier_map


def program_get_domain(prog: Program) -> islpy.UnionSet:
  instance_set = islpy.UnionSet.empty(
      islpy.Space.create_from_names(prog.ctx,
                                    set=[],
                                    params=prog.param_space_names))
  for _, stmt_id_name, stmt in iter_named_statements(prog):
    instance_set = instance_set.union(stmt.domain.set_tuple_name(stmt_id_name))
  return instance_set


def schedule_program(prog: Program) -> islpy.Schedule:
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
    prog: Program,
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
        for stmt_id, stmt_id_name, stmt in iter_named_statements(prog)
        if stmt_id in barrier_stmt_ids
    }
    schedule_map = schedule_map.remove_map_if(
        lambda m: m.get_tuple_name(islpy.dim_type.in_) in to_remove_statements)

  ast = ast_build.node_from_schedule_map(schedule_map)
  return ast

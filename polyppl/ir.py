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
#    BEGIN Utils
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


################################################################################
#    BEGIN ast Expression
################################################################################


def collect_free_vars(node: ast.AST):
  """Collects the free variables from node.

  Note that this function uses symtable,
  which requires potentially re-parsing from Python source.
  """
  if not isinstance(node, ast.Expression) and not isinstance(node, ast.Module):
    node = ast.Expression(body=node)
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
               rhs: ast.AST,
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

  def __copy__(self):
    cls = self.__class__
    result = cls.__new__(cls)
    result.__dict__.update(self.__dict__)
    return result

  def __deepcopy__(self, memo):
    cls = self.__class__
    result = cls.__new__(cls)
    memo[id(self)] = result
    for k, v in self.__dict__.items():
      if k not in {"domain", "lhs_proj"}:
        setattr(result, k, copy.deepcopy(v, memo))
      else:
        setattr(result, k, v)
    return result


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

  # TODO(camyang) make this a standalone parser
  # (https://github.com/lark-parser/lark/tree/master/examples/standalone)
  grammar_path = os.path.join(os.path.dirname(__file__), 'grammar.lark')
  with open(grammar_path, "r") as grammar:
    parser = Lark(grammar, propagate_positions=True)

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

    try:
      ir_ast = Program.parser.parse(src)
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

  def __copy__(self):
    cls = self.__class__
    result = cls.__new__(cls)
    result.__dict__.update(self.__dict__)
    return result

  def __deepcopy__(self, memo):
    cls = self.__class__
    result = cls.__new__(cls)
    memo[id(self)] = result
    for k, v in self.__dict__.items():
      if k not in {"ctx"}:
        setattr(result, k, copy.deepcopy(v, memo))
      else:
        setattr(result, k, v)
    return result

"""AST."""

from __future__ import annotations

from typing import NewType, List, Tuple, Optional, Dict, Sequence, Union, Set, Callable
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
from collections import defaultdict

from ordered_set import OrderedSet

from lark import Lark
import lark.exceptions

import islpy

import astor
import ast_scope

from polyppl.isl_utils import align_with_ids

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
               replace_map: Union[Callable[VarID, ast.Expression],
                                  Dict[VarID, ast.Expression]],
               node: ast.Expression,
               scope_info=None,
               *args,
               **kwargs):
    if isinstance(replace_map, dict):

      def replace(x):
        if x in replace_map:
          return replace_map[x]

      self.replace_map_fn = replace
    else:
      self.replace_map_fn = replace_map

    if scope_info is None:
      scope_info = ast_scope.annotate(node)
    self.scope_info = scope_info
    astor.TreeWalk.__init__(self, node=node, *args, **kwargs)

  def post_Name(self):
    node = self.cur_node
    if isinstance(self.scope_info[node], ast_scope.scope.GlobalScope):
      replace_with = self.replace_map_fn(node.id)
      if replace_with is not None:
        self.replace(replace_with)


def ast_replace_free_vars(
    node: ast.Expression, replacement_map: Union[Callable[VarID,
                                                          ast.Expression],
                                                 Dict[VarID, ast.Expression]]
) -> ast.Expression:
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


class AffineExpresionCollector(astor.TreeWalk):

  ExpressionKind = enum.Enum("ExpressionType", "affine_l1 affine_l2 non_affine")
  AnnotationMap = Dict[VarID, ExpressionKind]

  def __init__(self,
               domain_space_names: List[VarID],
               node: ast.Expression,
               scope_info=None,
               *args,
               **kwargs):
    if scope_info is None:
      scope_info = ast_scope.annotate(node)
    self.scope_info = scope_info
    self.domain_space_names = set(domain_space_names)
    self.annotation: AffineExpresionCollector.AnnotationMap = defaultdict(
        lambda: self.ExpressionKind.non_affine)
    astor.TreeWalk.__init__(self, node=node, *args, **kwargs)

  def is_affine_l1(self, node):
    return self.annotation[node] == self.ExpressionKind.affine_l1

  def is_affine_l2(self, node):
    return self.annotation[node] == self.ExpressionKind.affine_l2

  def is_affine(self, node):
    return self.annotation[node] != self.ExpressionKind.non_affine

  def post_BinOp(self):
    node = self.cur_node
    if not self.is_affine(node.left) or not self.is_affine(node.right):
      self.annotation[node] = self.ExpressionKind.non_affine
    elif isinstance(node.op, ast.Add) or isinstance(node.op, ast.Sub):
      if self.is_affine_l2(node.left) or self.is_affine_l2(node.right):
        self.annotation[node] = self.ExpressionKind.affine_l2
      else:
        self.annotation[node] = self.ExpressionKind.affine_l1
    elif isinstance(node.op, ast.Mult):
      if self.is_affine_l2(node.left) and self.is_affine_l2(node.right):
        self.annotation[node] = self.ExpressionKind.non_affine
      elif self.is_affine_l1(node.left) and self.is_affine_l1(node.right):
        self.annotation[node] = self.ExpressionKind.affine_l1
      else:
        self.annotation[node] = self.ExpressionKind.affine_l2
    elif isinstance(node.op, ast.FloorDiv):
      if self.is_affine_l1(node.right):
        self.annotation[node] = self.annotation[node.left]
      else:
        self.annotation[node] = self.ExpressionKind.non_affine
    else:
      self.annotation[node] = self.ExpressionKind.non_affine

  def post_Name(self):
    node = self.cur_node
    if isinstance(self.scope_info[node], ast_scope.scope.GlobalScope):
      if node.id in self.domain_space_names:
        self.annotation[node] = self.ExpressionKind.affine_l2
        return
    self.annotation[node] = self.ExpressionKind.non_affine

  def post_Num(self):
    node = self.cur_node
    self.annotation[node] = self.ExpressionKind.affine_l1


def aff_to_ast(aff: islpy.Aff, domain_space_names: List[VarID]) -> ast.AST:
  """Converts islpy.Aff into python AST."""
  aff = align_with_ids(aff, domain_space_names)
  coeffs = aff.get_coefficients_by_name(islpy.dim_type.in_)
  terms, signs = [], []
  for var, coeff in coeffs.items():
    if var == 1:
      coeff = coeff.floor().to_python()
      if coeff == 0:
        continue
      term = ast.Num(n=abs(coeff))
      sign = coeff > 0
    else:
      numerator = coeff.get_num_si()
      if numerator == 1:
        term = ast.Name(id=var, ctx=ast.Load())
      elif numerator == 0:
        continue
      else:
        term = ast.BinOp(left=ast.Num(n=abs(numerator)),
                         op=ast.Mult(),
                         right=ast.Name(id=var, ctx=ast.Load()))
      sign = numerator > 0
      try:
        denom = coeff.get_den_val().to_python()
        if denom != 1:
          term = ast.BinOp(left=term, op=ast.FloorDiv(), right=ast.Num(denom))
      except:
        raise ValueError(
            "Failed to cast multiaff due to denomerator not a python value")
    terms.append(term)
    signs.append(sign)

  if len(terms) > 0:
    aff_ast = terms[0]
    for term, sign in zip(terms[1:], signs[1:]):
      if sign > 0:
        op = ast.Add()
      else:
        op = ast.Sub()
      aff_ast = ast.BinOp(left=aff_ast, op=op, right=term)
  else:
    aff_ast = ast.Num(n=0)

  return aff_ast


def multi_aff_to_ast(multiaff: islpy.MultiAff,
                     domain_space_names: List[VarID]) -> List[ast.AST]:
  """Converts islpy.MultiAff into list of python ASTs."""
  multiaff = align_with_ids(multiaff, domain_space_names)
  aff_asts = []
  for i in range(multiaff.dim(islpy.dim_type.out)):
    aff = multiaff.get_at(i)
    aff_ast = aff_to_ast(aff, domain_space_names)
    aff_asts.append(aff_ast)
  return aff_asts


def ast_to_aff(ast: ast.AST, ctx: islpy.Context,
               domain_space_names: List[VarID],
               param_space_names: List[VarID]) -> islpy.Aff:
  # TODO(camyang) replace with something more robust
  ast_str = astor.to_source(ast).replace("//", "/")
  aff_str = "[{}] -> {{ [{}] -> [{}] }}".format(",".join(param_space_names),
                                                ",".join(domain_space_names),
                                                ast_str)
  return islpy.Aff.read_from_str(ctx, aff_str)


def asts_to_multi_aff(asts: List[ast.AST], ctx: islpy.Context,
                      domain_space_names: List[VarID],
                      param_space_names: List[VarID]) -> islpy.MultiAff:
  aff_list = islpy.AffList.alloc(ctx, len(asts))
  for ast in asts:
    aff_list.add(ast_to_aff(ast, ctx, domain_space_names, param_space_names))
  return islpy.MultiAff.from_aff_list(
      islpy.Space.create_from_names(ctx,
                                    in_=domain_space_names,
                                    params=param_space_names), aff_list)


def read_ast_to_map(
    read_ast: ast.AST, ctx: islpy.Context, domain_space_names: List[VarID],
    param_space_names: List[VarID],
    affine_annotation: AffineExpresionCollector.AnnotationMap
) -> islpy.BasicMap:
  if not isinstance(read_ast, ast.Subscript):
    raise TypeError("Invalid AST type")

  slic = read_ast.slice
  if isinstance(slic.value, ast.Tuple):
    # Multiple argument indexing
    if len(slic.value.elts) == 0:
      raise ValueError("Indexed defined array with empty "
                       "tuple is not allowed")
    else:
      targets = slic.value.elts
  else:
    # Single argument indexing
    targets = [slic.value]

  ret_bm = islpy.BasicMap.universe(
      islpy.Space.create_from_names(ctx,
                                    in_=domain_space_names,
                                    out=[],
                                    params=param_space_names))
  for target in targets:
    if (affine_annotation[target] ==
        AffineExpresionCollector.ExpressionKind.non_affine):
      bm_new_dim = islpy.BasicMap.universe(
          islpy.Space.create_from_names(ctx,
                                        in_=domain_space_names,
                                        out=["_"],
                                        params=param_space_names))
    else:
      aff = ast_to_aff(target, ctx, domain_space_names, param_space_names)
      bm_new_dim = islpy.BasicMap.from_aff(aff)
    ret_bm = ret_bm.flat_range_product(bm_new_dim)

  return ret_bm


class AffineExprWalker(astor.TreeWalk):

  def __init__(self,
               ctx: islpy.Context,
               domain_space_names: List[VarID],
               param_space_names: List[VarID],
               affine_annotation: AffineExpresionCollector.AnnotationMap,
               reads: Set[ast.AST],
               node: Optional[ast.Expression] = None,
               *args,
               **kwargs):
    self.ctx = ctx
    self.domain_space_names = domain_space_names
    self.param_space_names = param_space_names
    self.reads = reads
    self.affine_annotation = affine_annotation
    astor.TreeWalk.__init__(self, node=node, *args, **kwargs)

  def pre_any_node(self):
    node = self.cur_node
    if ((isinstance(node, ast.AST) and self.affine_annotation[node] !=
         AffineExpresionCollector.ExpressionKind.non_affine) and
        (not isinstance(self.parent, ast.AST) or
         self.affine_annotation[self.parent] ==
         AffineExpresionCollector.ExpressionKind.non_affine)):
      self.handle_identity_affine_expr()
      return True

  def post_any_node(self):
    pass

  class PatchedDict(defaultdict):

    def get(self, key, default=None):
      if default is not None:
        return super().get(key, default)
      else:
        return self[key]

  def setup(self):
    astor.TreeWalk.setup(self)
    self.pre_handlers = AffineExprWalker.PatchedDict(lambda: self.pre_any_node,
                                                     self.pre_handlers)
    self.post_handlers = AffineExprWalker.PatchedDict(
        lambda: self.post_any_node, self.post_handlers)

  def pre_Subscript(self):
    if self.cur_node in self.reads:
      self.handle_subscript_affine_expr()
      return True

  def handle_identity_affine_expr(self):
    pass

  def handle_subscript_affine_expr(self):
    pass


################################################################################
#    BEGIN Statement
################################################################################


class Statement(object):

  NonAffineConstraintLeftOrRight = enum.Enum("NonAffineConstraintLeftOrRight",
                                             "left right")

  class NonAffineConstraint(object):

    def __init__(self, left: ast.AST, right: ast.AST):
      self.left = left
      self.right = right

    def get(self,
            left_or_right: Statement.NonAffineConstraintLeftOrRight) -> ast.AST:
      if left_or_right == Statement.NonAffineConstraintLeftOrRight.left:
        return self.left
      else:
        return self.right

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
               non_affine_constraints: List[NonAffineConstraint] = [],
               histograms: Set[Tuple[
                   int,
                   Statement.NonAffineConstraintLeftOrRight]] = OrderedSet()):
    self.domain = domain
    self.param_space_names = param_space_names
    self.domain_space_names = domain_space_names
    self.lhs_array_name = lhs_array_name
    self.lhs_proj = lhs_proj
    self.op = op
    self.rhs = rhs
    self.non_affine_constraints = list(non_affine_constraints)
    self.histograms = OrderedSet(histograms)

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

  def set_histogramed(self, non_affine_idx: int,
                      left_or_right: Statement.NonAffineConstraintLeftOrRight):
    self.histograms.add((non_affine_idx, left_or_right))

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

    def safe_find_data(node, data: str, raise_if_not_found=True):
      try:
        return next(node.find_data(data))
      except StopIteration:
        if raise_if_not_found:
          raise Program.ProgramParseError("Cannot find {} in {}".format(
              data, node))
        else:
          return None

    try:
      ir_ast = Program.parser.parse(src)
    except lark.exceptions.LarkError:
      raise Program.ProgramParseError("Cannot parse")

    params = [
        VarID(param) for param in safe_find_data(ir_ast, "params").children
    ]
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

      # Parse rhs expression into python ast
      non_affine_constraints = safe_find_data(stmt_ast,
                                              "non_affine_guards",
                                              raise_if_not_found=False)
      if non_affine_constraints is None:
        non_affine_constraints = []
      else:
        non_affine_constraints = get_text_from_node(non_affine_constraints)
        # Remove leading whitespaces
        non_affine_constraints = non_affine_constraints.lstrip()
        non_affine_constraints = ast.parse(non_affine_constraints, mode="eval")
        if isinstance(non_affine_constraints.body, ast.Compare):
          compares = [non_affine_constraints.body]
        elif (isinstance(non_affine_constraints.body, ast.BoolOp) and
              isinstance(non_affine_constraints.body.op, ast.And)):
          compares = non_affine_constraints.body.values
        else:
          raise Program.ProgramParseError(
              "non_affine_constraints is not a valid python boolean conjunction"
          )
        non_affine_constraints = []
        for cmp_exp in compares:
          if isinstance(cmp_exp, ast.Compare) and len(
              cmp_exp.comparators) == 1 and isinstance(cmp_exp.ops[0], ast.Eq):
            left = cmp_exp.left
            right = cmp_exp.comparators[0]
            non_affine_constraints.append(
                Statement.NonAffineConstraint(left, right))
          else:
            raise Program.ProgramParseError(
                "non_affine_constraints is not a conjunction of equalities")

      prog.add_statement(
          Statement(domain,
                    param_space_names,
                    domain_space_names,
                    lhs_array_name,
                    rhs,
                    lhs_proj,
                    op=op,
                    non_affine_constraints=non_affine_constraints))
    return prog

  def stmt_name(self, stmt_id: StatementID):
    return "S{}".format(stmt_id)

  def iter_named_statements(self) -> Iterator[Tuple[int, str, Statement]]:
    for stmt_id, stmt in self.statements.items():
      yield stmt_id, self.stmt_name(stmt_id), stmt

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

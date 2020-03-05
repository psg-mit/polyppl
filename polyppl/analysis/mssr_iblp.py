"""MSSR formulation in docplex."""
from typing import List, Tuple, Callable

import itertools
import operator
import functools

import numpy as np
import islpy
import gurobipy as gp
GRB = gp.GRB

import polyppl.ir as ir
import polyppl.isl_utils as isl_utils
import polyppl.transformation.simplification_transformation as st
import polyppl.schedule as sched

ISL_SET_MAT_DIM_ORDER = [
    islpy.dim_type.set, islpy.dim_type.div, islpy.dim_type.param,
    islpy.dim_type.cst
]

ISL_DEP_MAT_DIM_ORDER = [
    islpy.dim_type.in_, islpy.dim_type.out, islpy.dim_type.div,
    islpy.dim_type.param, islpy.dim_type.cst
]


def add_np_mat_vars(model: gp.Model, shape, *args, **kwargs) -> np.ndarray:
  gp_vars = model.addVars(*shape, *args, **kwargs)
  ret = np.empty(shape, dtype=object)
  for coord, v in gp_vars.items():
    ret[coord] = v
  return ret


def basic_set_is_bounded(bs: islpy.BasicSet) -> bool:
  """Checks if the dimensions of a BasicSet are always bounded by constants.

  TODO(camyang) needs some rethinking the soundness of this operation.
  """
  return True


Term = Tuple[int]


def qpoly_to_sum_of_terms(qpoly: islpy.QPolynomial,
                          n_initial_params: int) -> List[Term]:
  ret = []
  for term in qpoly.get_terms():
    ret_term = []
    for i in range(n_initial_params):
      ret_term.append(term.get_exp(islpy.dim_type.param, i))
    ret.append(tuple(ret_term))
  return ret


def term_comparator_from_symbol_order(symbol_order: List[int]):

  def term_comparator(term1: Term, term2: Term) -> bool:
    term1 = tuple(term1[i] for i in symbol_order)
    term2 = tuple(term2[i] for i in symbol_order)
    if term1 > term2:
      return 1
    elif term1 < term2:
      return -1
    else:
      return 0

  return term_comparator


def bilp_schedule_build_gurobi_model(
    prog: ir.Program,
    schedule_dim: int,
    model_name="model",
    term_comparator: Callable[[Term, Term], bool] = None) -> gp.Model:
  deps = sched.compute_dependencies(prog)
  mdl = gp.Model("miqp")
  mdl.setParam("NonConvex", 2)

  n_params = len(prog.param_space_names)

  # create theta variables
  Theta = {}
  for _, stmt_name, stmt in prog.iter_named_statements():
    stmt_n_dim = stmt.domain.n_dim() + n_params + 1
    Theta[stmt_name] = {}
    for i, domain_bs in enumerate(stmt.domain.get_basic_sets()):
      theta_s = add_np_mat_vars(mdl, (schedule_dim, stmt_n_dim),
                                vtype=GRB.INTEGER,
                                name="Theta/{}/bs={}".format(stmt_name, i))
      Theta[stmt_name][domain_bs.set_tuple_name(stmt_name)] = theta_s

  # Constraints
  symb_name_to_var = {}
  for dep_map in isl_utils.union_map_get_maps(deps):
    n_symbs = dep_map.dim(islpy.dim_type.param) - n_params
    symb_names = dep_map.get_var_names(islpy.dim_type.param)[n_params:]
    for symb_name in symb_names:
      if symb_name not in symb_name_to_var:
        symb_name_to_var[symb_name] = mdl.addVar(vtype=GRB.INTEGER,
                                                 name=symb_name)
    symb_vars = np.array([symb_name_to_var[n] for n in symb_names])
    sym_vars_and_cst = np.append(symb_vars, [1])
    stmt_in_name = dep_map.get_tuple_name(islpy.dim_type.in_)
    stmt_out_name = dep_map.get_tuple_name(islpy.dim_type.out)

    dep_map_space = dep_map.get_space()
    param_space = dep_map_space.params()
    stmt_in_dim = dep_map_space.dim(islpy.dim_type.in_)
    stmt_out_dim = dep_map_space.dim(islpy.dim_type.out)

    for i, dep_bm in enumerate(dep_map.get_basic_maps()):
      for (in_domain, theta_in), (out_domain, theta_out) in itertools.product(
          Theta[stmt_in_name].items(), Theta[stmt_out_name].items()):
        dep_bm = dep_bm.intersect_domain(
            in_domain.align_params(param_space)).intersect_range(
                out_domain.align_params(param_space))
        if dep_bm.is_empty():
          continue
        theta_in_set, theta_in_param, theta_in_cst = (
            theta_in[:, :stmt_in_dim],
            theta_in[:, stmt_in_dim:stmt_in_dim + n_params], theta_in[:, -1:])
        theta_out_set, theta_out_param, theta_out_cst = (
            theta_out[:, :stmt_out_dim],
            theta_out[:, stmt_out_dim:stmt_out_dim + n_params], theta_out[:,
                                                                          -1:])

        dep_div_dim = dep_bm.dim(islpy.dim_type.div)

        dep_eq_mat = dep_bm.equalities_matrix(*ISL_DEP_MAT_DIM_ORDER)
        dep_ineq_mat = dep_bm.inequalities_matrix(*ISL_DEP_MAT_DIM_ORDER)
        dep_eq_mat, dep_ineq_mat = map(isl_utils.isl_mat_to_numpy,
                                       (dep_eq_mat, dep_ineq_mat))
        dep_mat = np.concatenate([dep_eq_mat, dep_ineq_mat])
        lambda_ = add_np_mat_vars(mdl, (schedule_dim, dep_mat.shape[0]),
                                  vtype=GRB.INTEGER,
                                  name='lambda/{}->{}/dep={}'.format(
                                      stmt_in_name, stmt_out_name, i))
        for k in range(schedule_dim):
          lambda_ineq_mv = gp.MVar(lambda_[k, dep_eq_mat.shape[0]:])
          mdl.addConstr(lambda_ineq_mv >= 0)

        del dep_eq_mat, dep_ineq_mat

        for k in range(schedule_dim):
          strongly_sat_p = mdl.addVar(
              lb=0,
              ub=schedule_dim - 1,
              vtype=GRB.INTEGER,
              name="strongly_sat_p/dim={}&dep={}".format(k, i))
          theta_in_set_k_mv = gp.MVar(theta_in_set[k])
          theta_out_set_k_mv = gp.MVar(theta_out_set[k])
          theta_in_param_k_mv = gp.MVar(theta_in_param[k])
          theta_out_param_k_mv = gp.MVar(theta_out_param[k])
          lambda_k_mv = gp.MVar(lambda_[k])
          idx = 0
          mdl.addConstr(
              theta_in_set_k_mv == dep_mat[:, idx:idx +
                                           stmt_in_dim].T @ lambda_k_mv)
          idx += stmt_in_dim
          mdl.addConstr(
              -theta_out_set_k_mv == dep_mat[:, idx:idx +
                                             stmt_out_dim].T @ lambda_k_mv)
          idx += stmt_out_dim
          mdl.addConstr(0 == dep_mat[:, idx:idx + dep_div_dim].T @ lambda_k_mv)
          idx += dep_div_dim
          mdl.addConstr((theta_in_param_k_mv - theta_out_param_k_mv) == (
              dep_mat[:, idx:idx + n_params].T @ lambda_k_mv))
          idx += n_params
          assert idx + n_symbs + 1 == dep_mat.shape[1]
          # add the cst constraint
          # that is:
          #  theta_S - theta_T - delta = lambda .* D .* [symb, N, 1]^T
          #
          delta_k = mdl.addVar(vtype=GRB.BINARY,
                               name="delta/dim={}&dep={}".format(k, i))
          need_sat = mdl.addVar(vtype=GRB.BINARY,
                                name="need_sat/dim={}&dep={}".format(k, i))
          mdl.addConstr((need_sat == 1) >> (k <= strongly_sat_p))
          mdl.addConstr((need_sat == 0) >> (k >= strongly_sat_p + 1))
          mdl.addConstr((delta_k == 1) >> (strongly_sat_p <= k))
          mdl.addConstr((delta_k == 0) >> (strongly_sat_p >= k + 1))
          lhs = theta_in_cst[k] - theta_out_cst[k] - delta_k
          rhs = (dep_mat[:, idx:].dot(sym_vars_and_cst).dot(lambda_[k]))
          tmp_var = mdl.addVar(vtype=GRB.INTEGER, name="indicator_quad_helper")
          mdl.addConstr(tmp_var == rhs)
          mdl.addConstr((need_sat == 1) >> (lhs[0] == tmp_var))

  # Objective
  if term_comparator is None:
    term_comparator = term_comparator_from_symbol_order(range(n_params))
  term_order_key_func = functools.cmp_to_key(term_comparator)

  all_domains = sched.program_get_domain(prog)
  print("Card...")
  all_domains_card = all_domains.card()
  print("done")
  ql = all_domains_card.get_pw_qpolynomial_list()
  if ql.n_pw_qpolynomial() != 1:
    raise ValueError("Multiple pieces polynomial not supported")
  all_domains_card = ql.get_at(0)
  domain_qpoly_pairs = []
  for card_domain, card_qpoly in all_domains_card.get_pieces():
    card_domain = card_domain.move_dims(islpy.dim_type.set, 0,
                                        islpy.dim_type.param, n_params,
                                        card_domain.n_param() - n_params)
    card_domain = [
        card_domain_bs for card_domain_bs in card_domain.get_basic_sets()
        if basic_set_is_bounded(card_domain_bs)
    ]
    if len(card_domain) == 0:
      continue
    qpoly_sum_of_terms = qpoly_to_sum_of_terms(card_qpoly, n_params)
    qpoly_max_term = max(qpoly_sum_of_terms, key=term_order_key_func)
    domain_qpoly_pairs.append((card_domain, qpoly_max_term))

  all_seen_qpolys = set(qst for _, qst in domain_qpoly_pairs)
  sorted_qpolys = {
      qpoly: i for i, qpoly in enumerate(
          sorted(all_seen_qpolys, key=term_order_key_func))
  }
  complexity_terms = []
  for card_domain, qpoly_max_term in domain_qpoly_pairs:
    qpoly_max_term_rank = sorted_qpolys[qpoly_max_term]
    for card_domain_bs in card_domain:
      card_domain_bs = card_domain_bs.project_out_all_params().get_basic_sets()
      assert len(card_domain_bs) == 1
      card_domain_bs = card_domain_bs[0]
      div_vars = mdl.addVars(card_domain_bs.dim(islpy.dim_type.div),
                             vtype=GRB.INTEGER,
                             name="div_vars").values()
      not_in_card_domain_indicator = mdl.addVar(vtype=GRB.BINARY,
                                                name="card_domain_indicator")
      complexity_term = mdl.addVar(vtype=GRB.CONTINUOUS)
      mdl.addConstr(complexity_term == (1 - not_in_card_domain_indicator) *
                    qpoly_max_term_rank)
      complexity_terms.append(complexity_term)
      eq_mat = isl_utils.isl_mat_to_numpy(
          card_domain_bs.equalities_matrix(*ISL_SET_MAT_DIM_ORDER))
      ineq_mat = isl_utils.isl_mat_to_numpy(
          card_domain_bs.inequalities_matrix(*ISL_SET_MAT_DIM_ORDER))
      symb_vars = np.array([
          symb_name_to_var[n]
          for n in card_domain_bs.get_var_names(islpy.dim_type.set)
      ] + div_vars + [1])
      disjunct_indictors = []
      eq_mat_mul_symb = eq_mat.dot(symb_vars)
      for c in eq_mat_mul_symb:
        gt_indicator = mdl.addVar(vtype=GRB.BINARY)
        lt_indicator = mdl.addVar(vtype=GRB.BINARY)
        mdl.addConstr((gt_indicator == 1) >> (c >= 1))
        mdl.addConstr((gt_indicator == 0) >> (c <= 0))
        mdl.addConstr((lt_indicator == 1) >> (c <= -1))
        mdl.addConstr((lt_indicator == 0) >> (c >= 0))
        disjunct_indictors += [gt_indicator, lt_indicator]
      ineq_mat_mul_symb = ineq_mat.dot(symb_vars)
      for c in ineq_mat_mul_symb:
        lt_indicator = mdl.addVar(vtype=GRB.BINARY)
        mdl.addConstr((lt_indicator == 1) >> (c <= -1))
        mdl.addConstr((lt_indicator == 0) >> (c >= 0))
        disjunct_indictors.append(lt_indicator)
      assert len(disjunct_indictors) > 0
      mdl.addConstr(not_in_card_domain_indicator == gp.or_(*disjunct_indictors))

  obj = mdl.addVar(name="objective")
  assert len(complexity_terms) > 0
  mdl.addConstr(obj == gp.max_(*complexity_terms))
  mdl.setObjective(obj, GRB.MINIMIZE)
  return mdl


def compute_effective_linear_space_symbolic(
    domain: islpy.Set, n_initial_params: int) -> islpy.BasicSet:
  """Computes the effective linear space of a symbolic domain.

  Args:
    - domain: a symbolic domain
    - n_initial_params: the first `n_initial_params` of `domain` are the actual
    parameters, the rest are treated as special symbols

  Returns:
    A symbolic basic set representing the effective linear space.
  """
  n_old_params = domain.n_param()
  domain_with_constant_shifts = domain
  for i in range(n_initial_params, n_old_params):
    domain_with_constant_shifts = domain_with_constant_shifts.lower_bound_val(
        islpy.dim_type.param, i, -1).upper_bound_val(islpy.dim_type.param, i, 1)
  domain_l_p = isl_utils.basic_set_zero(domain_with_constant_shifts.get_space())
  for i, bs in enumerate(domain_with_constant_shifts.get_basic_sets()):
    bs_l_p = isl_utils.compute_effective_linear_space(bs)
    domain_l_p = domain_l_p.union(bs_l_p)
  domain_l_p = domain_l_p.coalesce()
  return domain_l_p


def compute_reuse_set_for_statement_symbolic(
    prog: ir.Program, stmt_id: ir.Program.StatementID,
    share_space_map: st.RhsShareSpaceMapType):
  reduction = prog.get_statement_by_id(stmt_id)
  proj_kernel = isl_utils.compute_null_space(reduction.lhs_proj)
  share_space = share_space_map[stmt_id]
  effective_linear_space = compute_effective_linear_space_symbolic(
      reduction.domain, len(prog.param_space_names))
  reuse_set = share_space.intersect(effective_linear_space).subtract(
      proj_kernel)
  overlaping_set = islpy.BasicMap.from_domain_and_range(
      reduction.domain, reduction.domain).deltas()
  reuse_set = reuse_set.intersect(overlaping_set)
  return reuse_set


def sample_non_zero_reuse_vector_for_statement(
    prog: ir.Program, stmt_id: int,
    share_space_map: st.RhsShareSpaceMapType) -> islpy.MultiVal:
  reuse_set = compute_reuse_set_for_statement_symbolic(prog, stmt_id,
                                                       share_space_map)
  if reuse_set.is_empty():
    raise ValueError("Empty reuse set")
  return sample_vector_from_reuse_set_symbolic(reuse_set, "L{}".format(stmt_id))


def sample_vector_from_reuse_set_symbolic(
    reuse_set: islpy.Set,
    param_name_prefix: str) -> Tuple[islpy.MultiAff, islpy.Set]:
  """Samples a non zero vector from the symbolic reuse set.

  This is not doing any actual 'sampling'.
  Instead, we simply lift the set indices to new symbolic parameters.

  Args:
    reuse_set: the symbolic reuse set
    param_name_prefix: string prefix for names to be used for the new symbolic
    parameters

  Returns:
    A tuple (a, b)
    a: A MultiAff representing the symbolic reuse vector
    b: A Set representing the symbolic parameter constraint
  """
  n_old_params = reuse_set.n_param()
  n_new_params = reuse_set.n_dim()

  shift_params_names = ir.tmp_vars(basename=param_name_prefix, num=n_new_params)

  shift = islpy.MultiAff.identity_on_domain_space(reuse_set.get_space())
  shift = shift.add_dims(islpy.dim_type.param, n_new_params)
  for i in range(n_new_params):
    shift = shift.set_dim_name(islpy.dim_type.param, i + n_old_params,
                               shift_params_names[i])
    old_aff = shift.get_aff(i)
    shift = shift.set_aff(
        i,
        old_aff.add(
            islpy.Aff.var_on_domain(old_aff.get_domain_space(),
                                    islpy.dim_type.param, i + n_old_params)))

  reuse_set = isl_utils.align_with_ids(reuse_set, shift_params_names)
  shift_symb_param_domain = reuse_set.move_dims(islpy.dim_type.param,
                                                reuse_set.n_param(),
                                                islpy.dim_type.set, 0,
                                                reuse_set.n_dim())
  shift_symb_param_domain = shift_symb_param_domain.reset_space(
      shift_symb_param_domain.get_space().params())
  return shift, shift_symb_param_domain


def apply_symbolic_st(prog: ir.Program):
  unprocessed_reductions = [
      stmt_id for stmt_id, _, stmt in prog.iter_named_statements()
      if stmt.is_reduction
  ]
  _, share_space_map = st.compute_share_space(prog)
  st_count = 0
  while len(unprocessed_reductions) > 0:
    reduction_id = unprocessed_reductions.pop()
    reuse_set = compute_reuse_set_for_statement_symbolic(
        prog, reduction_id, share_space_map)
    if reuse_set.is_empty():
      continue
    reuse_set = reuse_set.union(isl_utils.basic_set_zero(reuse_set.get_space()))
    r_e, r_e_param_symb_domain = sample_vector_from_reuse_set_symbolic(
        reuse_set, "L{}".format(st_count))
    old_num_stmts = len(prog.statements)
    new_prog = st.simplification_transformation_core(prog, reduction_id, r_e,
                                                     r_e_param_symb_domain)
    new_num_stmts = len(new_prog.statements)
    new_stmt_ids = list(
        itertools.islice(reversed(new_prog.statements.keys()),
                         new_num_stmts - old_num_stmts))
    new_reduction_ids = [
        stmt_id for stmt_id in new_stmt_ids
        if new_prog.get_statement_by_id(stmt_id).is_reduction
    ]
    for new_reduction_id in new_reduction_ids:
      assert new_reduction_id not in share_space_map
      share_space_map[new_reduction_id] = share_space_map[reduction_id]
    unprocessed_reductions += new_reduction_ids
    st_count += 1
    prog = new_prog
  return prog


################################################################################
# BILP scheduling formulation
################################################################################

if __name__ == "__main__":
  prog = ir.Program.read_from_string("""
  N
  # A[i] += B[j] # { [i, j] : 0 <= i < N & 0 <= j & j < x2 & i < N - x1};
  A[i] += B[j+1] # { [i, j] : 0 <= i < N & 0 <= j < i};
  B[i+1] = A[i] # { [i] : 0 <= i < N};
  # A1[i] += B1[j] # { [i, j] : 0 <= i < N & 0 <= j < i};
  # B[i] = f(B[i]) # { [i] : 0 <= i < N };
  """)
  # domain = islpy.BasicSet("[N] -> { [i] : 0 <= i < N }")
  new_prog = apply_symbolic_st(prog)
  print(new_prog)
  mdl = bilp_schedule_build_gurobi_model(new_prog, 2)
  mdl.optimize()

  # def iterate_domain_faces(reduction: ir.Statement):

  #   proj_kernel = isl_utils.compute_null_space(reduction.lhs_proj)

  #   def iterate_domain_faces_recursive(domain: islpy.BasicSet,
  #                                      symb_domain: islpy.Set,
  #                                      n_initial_params: int,
  #                                      level=[0]) -> List[islpy.BasicSet]:

  #     n_new_params = domain.n_dim()
  #     n_old_params = domain.n_param()

  #     domain_l_p = symbolic_domain_compute_effective_linear_space(
  #         domain.intersect(symb_domain), n_initial_params)

  #     domain_reuse_space_no_zero = domain_l_p.subtract(
  #         proj_kernel.align_params(domain_l_p.get_space()))

  #     if domain_reuse_space_no_zero.intersect(symb_domain).is_empty():
  #       return [(domain, symb_domain)]

  #     domain_reuse_space = domain_reuse_space_no_zero.union(
  #         isl_utils.basic_set_zero(domain_reuse_space_no_zero.get_space()))

  #     shift_params_names = ir.tmp_vars(basename="L" +
  #                                      "".join([str(x) for x in level]),
  #                                      num=n_new_params)

  #     # the two steps below moves domain_l_p's set parameters to global parameters
  #     domain_reuse_space = isl_utils.align_with_ids(domain_reuse_space,
  #                                                   shift_params_names)
  #     domain_reuse_space = domain_reuse_space.move_dims(
  #         islpy.dim_type.param,
  #         domain_reuse_space.n_param(), islpy.dim_type.set, 0,
  #         domain_reuse_space.n_dim()).add_dims(islpy.dim_type.set, n_new_params)

  #     shift = islpy.MultiAff.identity_on_domain_space(domain.get_space())
  #     shift = shift.add_dims(islpy.dim_type.param, n_new_params)
  #     for i in range(n_new_params):
  #       shift = shift.set_dim_name(islpy.dim_type.param, i + n_old_params,
  #                                  shift_params_names[i])
  #       old_aff = shift.get_aff(i)
  #       shift = shift.set_aff(
  #           i,
  #           old_aff.add(
  #               islpy.Aff.var_on_domain(old_aff.get_domain_space(),
  #                                       islpy.dim_type.param, i + n_old_params)))
  #     shift_map = islpy.BasicMap.from_multi_aff(shift)
  #     domain = domain.align_params(shift.get_domain_space())
  #     shifted_domain = domain.apply(shift_map)
  #     inner_bodies = [(domain.intersect(shifted_domain),
  #                      domain_reuse_space.intersect(symb_domain))]
  #     outer_shell = (domain.subtract(shifted_domain)).make_disjoint()

  #     bs_symb_domain = domain_reuse_space.intersect(symb_domain)
  #     outer_shell = outer_shell.intersect(bs_symb_domain).make_disjoint()
  #     for i, bs in enumerate(outer_shell.get_basic_sets()):
  #       c = bs.intersect(bs_symb_domain)
  #       print(c)
  #       if c.is_empty():
  #         continue
  #       x = iterate_domain_faces_recursive(
  #           bs,
  #           domain_reuse_space.intersect(symb_domain),
  #           n_initial_params,
  #           level=level + [i])
  #       inner_bodies += x

  #     print("len", len(level), outer_shell.n_basic_set(), len(inner_bodies))
  #     return inner_bodies

  # domain = reduction.domain
  # return iterate_domain_faces_recursive(domain,
  #                                       islpy.BasicSet.universe(
  #                                           domain.get_space()),
  #                                       domain.n_param(),
  #                                       level=[0])
  # return iterate_domain_faces_recursive(
  #     domain,
  #     islpy.Set.read_from_str(
  #         domain.get_ctx(),
  #         "[N, x1, x2] -> { [i, j] : (x1 > 0 or x1 < 0) & x2 > 0 }"),
  #     1,
  #     level=[0])

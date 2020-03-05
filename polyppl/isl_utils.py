"""Utilities."""

from typing import Union, List, Iterator, TYPE_CHECKING

import numpy as np
import islpy

if TYPE_CHECKING:
  import polyppl.ir as ir


def set_align_dim_ids(set, names):
  assert len(names) == set.get_space().dim(islpy.dim_type.set)
  for pos, name in enumerate(names):
    set = set.set_dim_name(islpy.dim_type.set, pos, name)
  return set


def aff_align_in_ids(aff, names):
  assert len(names) == aff.get_space().dim(islpy.dim_type.in_)
  for i, name in enumerate(names):
    aff = aff.set_dim_name(islpy.dim_type.in_, i, name)
  return aff


def align_with_ids(obj: Union[islpy.BasicSet, islpy.Set, islpy.Aff,
                              islpy.MultiAff], names: List["ir.VarID"]):
  if isinstance(obj, islpy.Set) or isinstance(obj, islpy.BasicSet):
    return set_align_dim_ids(obj, names)
  elif isinstance(obj, islpy.MultiAff) or isinstance(obj, islpy.Aff):
    return aff_align_in_ids(obj, names)
  else:
    import pdb
    pdb.set_trace()
    raise TypeError("Invalid input")


def union_map_get_maps(um: islpy.UnionMap) -> Iterator[islpy.BasicMap]:
  ml = um.get_map_list()
  for i in range(ml.n_map()):
    yield ml.get_at(i)


def isl_mat_to_numpy(mat: islpy.Mat) -> np.array:
  ncols, nrows = mat.cols(), mat.rows()
  ret = np.empty((nrows, ncols), dtype=np.int32)
  for i in range(nrows):
    for j in range(ncols):
      ret[i, j] = mat.get_element_val(i, j).to_python()
  return ret


def set_all_tuple_names(umap, dim, name):
  ret = islpy.UnionMap.empty(umap.get_space())

  def set_name(map):
    nonlocal ret
    ret = ret.union(map.set_tuple_name(dim, name))

  umap.foreach_map(set_name)
  return ret


def bijective_basic_map_to_multi_aff(bm: islpy.BasicMap) -> islpy.MultiAff:
  if not bm.is_bijective():
    raise ValueError("BasicMap is not bijective")
  return islpy.PwMultiAff.from_map(bm).as_multi_aff()


def basic_set_zero(space: islpy.Space):
  """Returns set at zero, but without adding constraints on the parameters"""
  bs = islpy.BasicSet.universe(space)
  for i in range(bs.n_dim()):
    bs = bs.fix_val(islpy.dim_type.set, i, islpy.Val.zero(bs.get_ctx()))
  return bs


def basic_set_remove_zero(bs: islpy.BasicSet) -> islpy.Set:
  return bs.subtract(basic_set_zero(bs.get_space()))


def point_to_multi_val(point: islpy.Point) -> islpy.MultiVal:
  ndim = point.get_space().dim(islpy.dim_type.set)
  vallist = islpy.ValList.alloc(point.get_ctx(), ndim)
  for i in range(ndim):
    val = point.get_coordinate_val(islpy.dim_type.set, i)
    vallist = vallist.add(val)
  return islpy.MultiVal.from_val_list(point.get_space(), vallist)


def compute_null_space(bf: islpy.MultiAff) -> islpy.BasicSet:
  """Computes null space of function.

  Given affine function f(a) = b, compute {x | forall u, f(u) = f(u + x) }
  """
  bm = islpy.BasicMap.from_multi_aff(bf)
  null_map = bm.apply_range(bm.reverse())
  null_set = basic_set_zero(null_map.get_space().domain()).apply(null_map)
  return null_set


def compute_proj_kernel(proj: islpy.MultiAff) -> islpy.BasicSet:
  bm = islpy.BasicMap.from_multi_aff(proj)
  proj_kernel = basic_set_zero(bm.get_space().range()).apply(bm.reverse())
  return proj_kernel


def compute_lineality_space(bs: islpy.BasicSet) -> islpy.BasicSet:
  """Computes lineality space of set.

  The lineality space of s := { z | Qz + q >= 0 } is defined as { z | Q z = 0}
  """
  dims = [
      islpy.dim_type.set, islpy.dim_type.div, islpy.dim_type.param,
      islpy.dim_type.cst
  ]
  eq_mat = bs.equalities_matrix(*dims)
  ineq_mat = bs.inequalities_matrix(*dims)

  n_cst = bs.n_param() + 1

  def drop_cst_col(mat: islpy.Mat) -> islpy.Mat:
    mat = mat.drop_cols(mat.cols() - n_cst, n_cst)
    mat = mat.add_zero_cols(n_cst)
    return mat

  eq_mat = drop_cst_col(eq_mat)
  ineq_mat = drop_cst_col(ineq_mat)
  ret_eq_mat = eq_mat.concat(ineq_mat)
  ret_ineq_mat = islpy.Mat.alloc(bs.get_ctx(), 0, ret_eq_mat.cols())

  return islpy.BasicSet.from_constraint_matrices(bs.get_space(), ret_eq_mat,
                                                 ret_ineq_mat, *dims)


def bs_from_kernel_of_constraints(
    space: islpy.Space, constraints: List[islpy.Constraint]) -> islpy.BasicSet:
  """Computes the intersection of all kernels of constraints."""
  ret = islpy.BasicSet.universe(space)
  zero = islpy.Val.zero(space.get_ctx())
  for c in constraints:
    # Set const and param coeffs to be 0 and create a equality constraint
    # This effectively means we treat parameteres as constants
    # and given constraint Qz + q >=0, we use kernel(Q) as our L_p constraint
    kernel_constraint = islpy.Constraint.equality_from_aff(
        c.get_aff().set_constant_val(zero).set_coefficients(
            islpy.dim_type.param, [zero] * space.dim(islpy.dim_type.param)))
    ret = ret.add_constraint(kernel_constraint)
  return ret


def compute_effective_linear_space(bs: islpy.BasicSet) -> islpy.BasicSet:
  r"""Compute the space where bs is unbounded.

  The linear space L_p for P = {z | Qz + q >= 0} is defined as the set of
  vectors v such that for all k, P \cap shift(P, k+v) != empty.
  Intuitively, this is the set of vectors where P spans indefinitely (where we
  consider P's parameters to be possibiliy infinite).
  """
  effective_saturated_constraints = []
  for constraint in bs.get_constraints():
    aff = constraint.get_aff()
    tau = bs.max_val(aff)
    if not tau.is_infty():
      effective_saturated_constraints.append(constraint)
  return bs_from_kernel_of_constraints(bs.get_space(),
                                       effective_saturated_constraints)


def compute_saturated_constraints(bs: islpy.BasicSet) -> List[islpy.Constraint]:
  """Computes the saturated constraints.

  A constraint c is saturated if (c^-1) & P == P.
  """
  ret = []
  for c in bs.get_constraints():
    if c.is_equality():
      ret.append(c)
    else:
      bs_test = bs.add_constraint(
          islpy.Constraint.inequality_from_aff(c.get_aff().neg()))
      if bs_test == bs:
        ret.append(c)
  return ret


def compute_boundary_constraint(bs: islpy.BasicSet,
                                proj: islpy.MultiAff,
                                non_boundary=False) -> List[islpy.Constraint]:
  """Computes boundary constraint of set given project function.

  Args:
    bs: the input basic set.
    proj: the input projection represented as a MultiAff.
    non_boundary: if True, returns the non-boundary constraints instead of the
      boundary constraints.

  Returns:
    boundary constraint or non-boundary constraints.
  """
  proj_kernel = compute_proj_kernel(proj)
  saturated_constraints = compute_saturated_constraints(bs)
  hp = bs_from_kernel_of_constraints(bs.get_space(), saturated_constraints)
  boundary_constraints = []
  for c in bs.get_constraints():
    c_kernel = bs_from_kernel_of_constraints(bs.get_space(), [c])
    is_boundary = hp.intersect(c_kernel).is_subset(hp.intersect(proj_kernel))
    if non_boundary != is_boundary:
      boundary_constraints.append(c)
  return boundary_constraints


def compute_non_boundary_constraint(
    bs: islpy.BasicSet, proj: islpy.MultiAff) -> List[islpy.Constraint]:
  return compute_boundary_constraint(bs, proj, True)


if __name__ == "__main__":
  ctx = islpy.Context()
  a = islpy.BasicSet.read_from_str(
      ctx, "[N, M] -> {[i, j] : 0 <= i < N & 0 < j < M}")
  proj = islpy.MultiAff.read_from_str(ctx, "[N, M] -> { [i, j] -> [i] }")
  # b = compute_lineality_space(a)
  # print(b)
  print(compute_non_boundary_constraint(a, proj))

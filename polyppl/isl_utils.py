"""Utilities."""

from typing import Union, Optional, List

import islpy


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
                              islpy.MultiAff], names: List[str]):
  if isinstance(obj, islpy.Set) or isinstance(obj, islpy.BasicSet):
    return set_align_dim_ids(obj, names)
  elif isinstance(obj, islpy.MultiAff) or isinstance(obj, islpy.Aff):
    return aff_align_in_ids(obj, names)
  else:
    import pdb
    pdb.set_trace()
    raise TypeError("Invalid input")


def set_all_tuple_names(umap, dim, name):
  ret = islpy.UnionMap.empty(umap.get_space())

  def set_name(map):
    nonlocal ret
    ret = ret.union(map.set_tuple_name(dim, name))

  umap.foreach_map(set_name)
  return ret


def basic_set_zero(space: islpy.Space):
  """Returns set at zero, but without adding constraints on the parameters"""
  bs = islpy.BasicSet.universe(space)
  for i in range(bs.n_dim()):
    bs = bs.fix_val(islpy.dim_type.set, i, islpy.Val.zero(bs.get_ctx()))
  return bs


def point_to_multi_val(point: islpy.Point) -> islpy.MultiVal:
  ndim = point.get_space().dim(islpy.dim_type.set)
  vallist = islpy.ValList.alloc(point.get_ctx(), ndim)
  for i in range(ndim):
    val = point.get_coordinate_val(islpy.dim_type.set, i)
    vallist = vallist.add(val)
  return islpy.MultiVal.from_val_list(point.get_space(), vallist)
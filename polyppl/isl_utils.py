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

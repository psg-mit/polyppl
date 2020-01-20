"""Patch islpy and ISL.

This module is really not desirable.
Consider removing this module after ISL exposes necessary interface.

Ref: https://github.com/inducer/islpy/issues/21
"""

from typing import List

from cffi import FFI

import islpy
from islpy._isl import ffi
from islpy._isl import lib as isl_ffi_lib

_ffi = FFI()
_ffi.cdef("""
typedef struct {
  int ref;
	void *ctx;

	int n;

	size_t size;
	void *p[0];
} isl_ast_node_list;
""")


def isl_ast_node_block_get_children(node: islpy.AstNode) -> List[islpy.AstNode]:
  ast_node_list_ptr = isl_ffi_lib.isl_ast_node_block_get_children(node.data)
  ast_node_list_ptr = _ffi.cast("isl_ast_node_list*", ast_node_list_ptr)
  ret = []
  for i in range(ast_node_list_ptr.n):
    ast_child_node_ptr = ffi.cast("struct isl_ast_node *",
                                  (ast_node_list_ptr.p + i)[0])
    ast_child_node = islpy.AstNode(
        isl_ffi_lib.isl_ast_node_copy(ast_child_node_ptr))
    ret.append(ast_child_node)
  ast_node_list_ptr.ref -= 1
  return ret

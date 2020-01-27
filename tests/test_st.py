import unittest

import astor
import islpy

import polyppl.ir as ir
import polyppl.code_gen as code_gen
import polyppl.transformation.simplification_transformation as st

from tests.base import PolyPPLTestCaseBase


class TestIR(PolyPPLTestCaseBase):

  def test_st_transformation_equivalence(self):
    prog_str = """
    N
    A[i] += B[j]   # { [i, j] : 0 <= i < N & 0 <= j < i } ;
    B[i] = f(A[i]) # { [i] : 0 <= i < N } ;
    """
    prog = ir.Program.read_from_string(prog_str, self.isl_ctx)
    ast1 = code_gen.prog_to_ast(prog)
    prog_st = st.simplification_transformation(
        prog, 0, islpy.MultiVal.read_from_str(self.isl_ctx, "{ [-1, 0] }"))
    ast2 = code_gen.prog_to_ast(prog_st)
    print(astor.to_source(ast1, indent_with=' ' * 2))
    print(astor.to_source(ast2, indent_with=' ' * 2))


if __name__ == "__main__":
  unittest.main()

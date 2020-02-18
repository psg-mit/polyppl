import unittest

import astor
import islpy

import polyppl.ir as ir
import polyppl.code_gen as code_gen
import polyppl.transformation.histogram as histogram
import polyppl.transformation.simplification_transformation as st

from tests.base import PolyPPLTestCaseBase


class TestIR(PolyPPLTestCaseBase):

  # def test_simple(self):
  #   prog_str = """
  #   N
  #   # test comment
  #   A[i] += f(B[j])     # { [i, j] : 0 <= i < N & 0 <= j < i } ;
  #   B[i] max= f(A[i])   # { [i] : 0 <= i < N & i % 2 = 0 } ;
  #   C[i, j+k] += g(A[i+k, j+k] + B[j]) # { [i, j, k] : 0 <= i < N & 0 <= j < i * 2 &  j <= k < i & k % 3 = 2  } ;
  #   """
  #   ast = code_gen.prog_str_to_ast(prog_str)

  # def test_guass_siedel(self):
  #   prog_str = """
  #   # Guass-Seidel
  #   N T
  #   sigma1[i, t] += A[i, j] * x_new[j, t] # {[j, i, t] : 0 <= i < N & 0 <= j < N & j < i & 0 <= t < T};
  #   sigma2[i, t] += A[i, j] * x[j, t]   # {[i, j, t] : 0 <= i < N & 0 <= j < N & i < j & 0 <= t < T};
  #   x_new[i, t] = (b[i] - sigma1[i, t] - sigma2[i, t]) / A[i, i] # {[i, t] : 0 <= i < N & 0 <= t < T};
  #   x[i,t+1] = x_new[i, t] # {[i, t] : 0 <= i < N & 0 <= t < T - 1};
  #   """
  #   ast = code_gen.prog_str_to_ast(prog_str)

  # def test_circular_dep(self):
  #   prog_str = """
  #   N
  #   A[i] = f(B[i])     # { [i] : 0 <= i < N };
  #   B[i+1] = g(A[i])   # { [i] : 0 <= i < N };
  #   """
  #   ast = code_gen.prog_str_to_ast(prog_str)
  #   print(astor.to_source(ast))

  # def test_non_affine_constraint(self):
  #   prog_str = """
  #   N
  #   A[i] = f(B[i])     # { [i] : 0 <= i < N } & a[i] == z[j] ;
  #   B[i+1] = g(A[i])   # { [i] : 0 <= i < N };
  #   """
  #   ast = code_gen.prog_str_to_ast(prog_str)
  #   print(astor.to_source(ast))

  def test_histogram(self):
    prog_str = """
    N
    A[i] += f(B[j])     # { [i, j] : 0 <= i < N & 0 <= j < i } & x[i] == t[j];
    B[i] = g(A[i])    # { [i] : 0 <= i < N };
    """
    prog = ir.Program.read_from_string(prog_str, self.isl_ctx)
    ast = code_gen.prog_to_ast(prog)
    print(astor.to_source(ast))
    prog = histogram.histogram(
        prog, "A", 0, ir.Statement.NonAffineConstraintLeftOrRight.right)
    prog_st = st.simplification_transformation(
        prog, 0, islpy.MultiVal.read_from_str(self.isl_ctx, "{ [-1, 0] }"))
    ast = code_gen.prog_to_ast(prog_st)
    import pdb
    pdb.set_trace()
    print(astor.to_source(ast))


if __name__ == '__main__':
  unittest.main()

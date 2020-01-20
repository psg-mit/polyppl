import unittest

import islpy
from polyppl.ir import *  # pylint: disable=unused-wildcard-import


class TestIR(unittest.TestCase):

  def setUp(self):
    self.isl_ctx = islpy.Context()
    self.isl_ctx.set_on_error(1)  # continue then raise exception

  def test_affine_expression_cast(self):
    exp = AffineExpression("+", [
        AffineExpression("+", [
            RefExpression("x"),
            AffineExpression("+", [
                RefExpression("y"),
                AffineExpression("+", [
                    OpExpression("-", [RefExpression("z")]),
                    ConstExpression(1)
                ])
            ])
        ])
    ])
    aff_exp = expression_to_isl(exp, ["x", "y"], params=["z"], ctx=self.isl_ctx)
    aff_exp_correct = islpy.Aff.read_from_str(
        self.isl_ctx, "[z] -> { [x, y] -> [x + y - z + 1] }")
    self.assertEqual(aff_exp, aff_exp_correct)

  def test_ir_parse_correct(self):
    prog = """N M
    A[i] += B[j] # {[i, j] : 0 <= i < N & 0 <= j < i};
    X[i, (2*j+i//2)//2] = f(g(i), j) # { [j, i]: 0 <= i < N & 0 <= j < N };
    """
    prog1 = Program.read_from_string(prog, ctx=self.isl_ctx)
    prog2 = Program.read_from_string(repr(prog1))
    self.assertEqual(prog1, prog2)

  def test_ir_parse_rejects_incorrect(self):
    progs = []

    # Invalid syntax
    progs.append("""N M
    A[i] += B[i] # { [i] :  }
    """)

    # domain mismatch 1
    progs.append("""N M
    A[i, j] = B[j] # { [i] :  };
    """)

    # domain mismatch 2
    progs.append("""N M
    A[i] = B[j] # { [i] :  };
    """)

    # lhs_proj not valid
    progs.append("""
    A[i, k] = B[k] # { [i, j, k]: i < k };
    """)

    # Missing param
    progs.append("""
    A[i, k] += B[k] # { [i, j, k]: i < k && i < N };
    """)

    for i, prog in enumerate(progs):
      with self.subTest(i=i):
        self.assertRaises(
            Program.ProgramParseError,
            (lambda: Program.read_from_string(prog, self.isl_ctx)))


if __name__ == '__main__':
  unittest.main()

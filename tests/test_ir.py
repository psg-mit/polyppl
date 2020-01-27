import unittest

import islpy
from polyppl.ir import *  # pylint: disable=unused-wildcard-import

from tests.base import PolyPPLTestCaseBase


class TestIR(PolyPPLTestCaseBase):

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
    A[i*i] = B[j] # { [i] :  };
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

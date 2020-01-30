import unittest

import islpy

import polyppl.ir as ir
import polyppl.transformation.simplification_transformation as st

from tests.base import PolyPPLTestCaseBase


class TestIR(PolyPPLTestCaseBase):

  def _test_single(self, prog: str, reuse: str):
    prog = ir.Program.read_from_string(prog, ctx=self.isl_ctx)
    rs_computed = st.compute_reuse_space(prog)[0]["X"]
    rs = islpy.BasicSet.read_from_str(self.isl_ctx, reuse)
    self.assertEqual(rs_computed, rs)

  def test_ir_parse_correct(self):
    # yapf: disable
    test_cases = [
      (
        """N M
        X[i, j] = f(g(i+j)) # { [j, i]: 0 <= i < N & 0 <= j < N };
        """,
        "[N, M] -> { [a, b] : a + b = 0}"
      ),
      (
        """
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : 2*i+j = 0 }"
      ),
      (
        """
        A[i] = 1 # { [i] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : }"
      ),
      (
        """
        A[i] = B[i] # { [i] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : 2*i+j = 0}"
      ),
      (
        """
        A[i] += B[j] # { [i, j] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : }"
      ),
      (
        """
        A[i] += B[i+j, -j] # { [i, j] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : 2*i+j = 0}"
      ),
      (
        """
        A[i] += B[0] # { [i, j] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : }"
      ),
      (
        """
        A[i] += B[B[i+j]] # { [i, j] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : }"
      ),
      (
        """
        A[i] += B[B[j] + (2 * j + 5)] # { [i, j] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : }"
      ),
      (
        """
        A[i] += B[B[j] + (2 * j + i + 5)] # { [i, j] : 0 < i < j < 5} ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : 2 * i + j = 0 }"
      ),
      (
        """
        A[i] += X[i, j] # { [i, j] : } ;
        X[i, j] = A[2*i+j] # { [i, j]:  };
        """,
        "{ [i, j] : 2 * i + j = 0}"
      ),
      (
        """
        X[i, j] = B[j+j] # { [i, j] };
        X[i, j] = A[i] # { [i, j] };
        """,
        "{ [0, 0] : }"
      ),
      (
        """N
        A[i] += B[j] # { [i, j] : 0 <= i < N & 0 <= j};
        X[i] = A[i] # { [i] };
        """,
        "{ [i] : }"
      ),
    ]
    # yapf: enable

    for i, (prog, rs) in enumerate(test_cases):
      with self.subTest(i=i):
        self._test_single(prog, rs)


if __name__ == '__main__':
  unittest.main()

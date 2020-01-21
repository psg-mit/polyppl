import unittest

import islpy
from polyppl.ir import *  # pylint: disable=unused-wildcard-import
from polyppl.code_gen import isl_ast_code_gen


class TestIR(unittest.TestCase):

  def setUp(self):
    self.isl_ctx = islpy.Context()
    self.isl_ctx.set_on_error(1)  # continue then raise exception

  def test_simple(self):
    prog = Program.read_from_string("""
    N
    # test comment
    A[i] += f(B[j])     # { [i, j] : 0 <= i < N & 0 <= j < i } ;
    B[i] max= f(A[i])   # { [i] : 0 <= i < N & i % 2 = 0 } ;
    C[i, j+k] += g(A[i+k, j+k] + B[j]) # { [i, j, k] : 0 <= i < N & 0 <= j < i * 2 &  j <= k < i & k % 3 = 2  } ;
    """)
    prog = Program.read_from_string("""
    # Guass-Seidel
    N T
    sigma1[i, t] += A[i, j] * x_new[j, t] # {[j, i, t] : 0 <= i < N & 0 <= j < N & j < i & 0 <= t < T};
    sigma2[i, t] += A[i, j] * x[j, t]   # {[i, j, t] : 0 <= i < N & 0 <= j < N & i < j & 0 <= t < T};
    x_new[i, t] = (b[i] - sigma1[i, t] - sigma2[i, t]) / A[i, i] # {[i, t] : 0 <= i < N & 0 <= t < T};
    x[i,t+1] = x_new[i, t] # {[i, t] : 0 <= i < N & 0 <= t < T - 1};
    """)
    # writes = collect_writes(prog)
    # reads = collect_reads(prog)
    # dependencies = writes.apply_range(reads.reverse())
    new_prog, barrier_map = inject_reduction_barrier_statements(prog)
    # new_prog, barrier_map = prog, None
    schedule = schedule_program(new_prog)
    isl_ast = schedule_isl_ast_gen(new_prog, schedule, barrier_map=barrier_map)
    cgen_ast = isl_ast_code_gen(prog, isl_ast)
    # print(astor.dump_tree(cgen_ast))
    print(astor.to_source(cgen_ast))


if __name__ == '__main__':
  unittest.main()

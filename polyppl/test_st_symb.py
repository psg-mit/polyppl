import islpy

import polyppl.transformation.simplification_transformation as st
import polyppl.ir as ir

ctx = islpy.Context()
prog = ir.Program.read_from_string(
    """
N
A[i] += B[j] # { [i, j]: 0 <= i < N & 0 <= j < i};
""", ctx)
r_e = islpy.MultiAff.read_from_str(ctx, "[N, u, v] -> { [i, j] -> [i+u, j+v] }")
prog2 = st.simplification_transformation_core(prog, 0, r_e)
print(prog2)
import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Datapoints", "Mus"]).params()

prog = Program(param_space)\
.add_stmt(
    "_ret3_", ["k", "mu"],
    ConstExp("Mus"),
    "[Datapoints, Mus] -> { [k, mu] : 0 <= k < Datapoints && 0 <= mu < Mus }"
).add_stmt(
    "q_new", ["k"],
    AccessExp("_ret3_", IdExp("k"), IdExp("mu")),
    "[Datapoints, Mus] -> { [k, mu] : 0 <= k < Datapoints && 0 <= mu < Mus }",
    op="sample"
)\
.add_stmt(
    "acc7", ["k"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z", IdExp("i")), AccessExp("z", IdExp("k")), "Mu")
    ]
)\
.add_stmt(
    "acc8", ["k"],
    ConstExp(1),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z", IdExp("i")), AccessExp("z", IdExp("k")), "Mu")
    ]
)\
.add_stmt(
    "acc3", ["k"],
    OpExp("f", AccessExp("obs", IdExp("k")), AccessExp("acc7", IdExp("k")), AccessExp("acc8", IdExp("k"))),
    '[Datapoints, Mus] -> { [k] : 0 <= k < Datapoints }',
)

cost_evaluator = PolyhedralCardExactCostEvaluator({'Datapoints': 10000, 'Mus': 10})

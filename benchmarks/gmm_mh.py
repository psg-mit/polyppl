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
    "acc5__1", ["k"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("q_new", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc5__2", ["k"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("q_new", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc5_", ["k"],
    OpExp("+", AccessExp("acc5__1", IdExp("k")), AccessExp("acc5__2", IdExp("k"))),
    '[Datapoints, Mus] -> { [k] : 0 <= k < Datapoints }',
)\
\
.add_stmt(
    "acc6__1", ["k"],
    ConstExp(1),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("q_new", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc6__2", ["k"],
    ConstExp(1),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("q_new", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc6_", ["k"],
    OpExp("+", AccessExp("acc6__1", IdExp("k")), AccessExp("acc6__2", IdExp("k"))),
    '[Datapoints, Mus] -> { [k] : 0 <= k < Datapoints }',
)\
\
.add_stmt(
    "acc9__1", ["k"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("z_old", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc9__2", ["k"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc9_", ["k"],
    OpExp("+", AccessExp("acc9__1", IdExp("k")), AccessExp("acc9__2", IdExp("k"))),
    '[Datapoints, Mus] -> { [k] : 0 <= k < Datapoints }',
)\
\
.add_stmt(
    "acc10__1", ["k"],
    ConstExp(1),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("z_old", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc10__2", ["k"],
    ConstExp(1),
    '[Datapoints, Mus] -> { [k, i] : 0 <= k < Datapoints && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Mus")
    ]
).add_stmt(
    "acc10_", ["k"],
    OpExp("+", AccessExp("acc10__1", IdExp("k")), AccessExp("acc10__2", IdExp("k"))),
    '[Datapoints, Mus] -> { [k] : 0 <= k < Datapoints }',
)\
\
.add_stmt(
    "ret8", ["k"],
    OpExp("f1", AccessExp("acc9_", IdExp("k")), AccessExp("acc10_", IdExp("k")), AccessExp("obs", IdExp("k"))),
    '[Datapoints, Mus] -> { [k] : 0 <= k < Datapoints }'
).add_stmt(
    "z_new", ["k"],
    OpExp("f", AccessExp("ret8", IdExp("k")), AccessExp("acc5_", IdExp("k")), AccessExp("acc6_", IdExp("k")), AccessExp("q_new", IdExp("k"))),
    '[Datapoints, Mus] -> { [k] : 0 <= k < Datapoints }'
)


cost_evaluator = PolyhedralCardExactCostEvaluator({'Datapoints': 10000, 'Mus': 10})

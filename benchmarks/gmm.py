import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Datapoints", "Mu"]).params()

prog = Program(param_space)\
.add_stmt(
    "acc645__1", ["k", "mu1"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mu] -> { [k, mu1, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("mu1"), "Mu")
    ]
).add_stmt(
    "acc645__2", ["k", "mu1"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mu] -> { [k, mu1, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("mu1"), "Mu")
    ]
).add_stmt(
	"acc645_", ["k", "mu1"],
	OpExp("+", AccessExp("acc645__1", IdExp("k"), IdExp("mu1")), AccessExp("acc645__2", IdExp("k"), IdExp("mu1"))),
    '[Datapoints, Mu] -> { [k, mu1] : 0 <= k < Datapoints && 0 <= mu1 < Mu }',
)\
\
.add_stmt(
    "acc646__1", ["k", "mu1"],
    ConstExp(1),
    '[Datapoints, Mu] -> { [k, mu1, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("mu1"), "Mu")
    ]
).add_stmt(
    "acc646__2", ["k", "mu1"],
    ConstExp(1),
    '[Datapoints, Mu] -> { [k, mu1, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("mu1"), "Mu")
    ]
).add_stmt(
	"acc646_", ["k", "mu1"],
	OpExp("+", AccessExp("acc646__1", IdExp("k"), IdExp("mu1")), AccessExp("acc646__2", IdExp("k"), IdExp("mu1"))),
    '[Datapoints, Mu] -> { [k, mu1] : 0 <= k < Datapoints && 0 <= mu1 < Mu }',
)\
\
\
.add_stmt(
    "acc651__1", ["k", "mu1", "mu2"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mu] -> { [k, mu1, mu2, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("mu2"), "Mu")
    ]
).add_stmt(
    "acc651__2", ["k", "mu1", "mu2"],
    AccessExp("obs", IdExp("i")),
    '[Datapoints, Mu] -> { [k, mu1, mu2, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("mu2"), "Mu")
    ]
).add_stmt(
    "acc651_", ["k", "mu1", "mu2"],
    OpExp("+", AccessExp("acc651__1", IdExp("k"), IdExp("mu1"), IdExp("mu2")), AccessExp("acc651__2", IdExp("k"), IdExp("mu1"), IdExp("mu2"))),
    '[Datapoints, Mu] -> { [k, mu1, mu2] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu }',
)\
\
.add_stmt(
    "acc652__1", ["k", "mu1", "mu2"],
    ConstExp(1),
    '[Datapoints, Mu] -> { [k, mu1, mu2, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("mu2"), "Mu")
    ]
).add_stmt(
    "acc652__2", ["k", "mu1", "mu2"],
    ConstExp(1),
    '[Datapoints, Mu] -> { [k, mu1, mu2, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu && k < i < Datapoints }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("mu2"), "Mu")
    ]
).add_stmt(
    "acc652_", ["k", "mu1", "mu2"],
    OpExp("+", AccessExp("acc652__1", IdExp("k"), IdExp("mu1"), IdExp("mu2")), AccessExp("acc652__2", IdExp("k"), IdExp("mu1"), IdExp("mu2"))),
    '[Datapoints, Mu] -> { [k, mu1, mu2] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu }',
)\
\
\
.add_stmt(
	"_ret649_", ["k", "mu1", "mu2"],
	OpExp("f1", AccessExp("obs", IdExp("k")), AccessExp("acc651_", IdExp("k"), IdExp("mu1"), IdExp("mu2")), AccessExp("acc652_", IdExp("k"), IdExp("mu1"), IdExp("mu2"))),
    '[Datapoints, Mu] -> { [k, mu1, mu2] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu }',
).add_stmt(
	"logsum_ret649_", ["k", "mu1"],
	AccessExp("_ret649_", IdExp("k"), IdExp("mu1"), IdExp("mu2")),
    '[Datapoints, Mu] -> { [k, mu1, mu2] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= mu2 < Mu }',
    op="unknown"
).add_stmt(
	"_ret643_", ["k", "mu1"],
	OpExp("f1", AccessExp("obs", IdExp("k")), AccessExp("acc645_", IdExp("k"), IdExp("mu1")), AccessExp("acc646_", IdExp("k"), IdExp("mu1")), AccessExp("logsum_ret649_", IdExp("k"), IdExp("mu1"))),
    '[Datapoints, Mu] -> { [k, mu1] : 0 <= k < Datapoints && 0 <= mu1 < Mu }',
).add_stmt(
	"z_new", ["k"],
	AccessExp("_ret643_", IdExp("k"), IdExp("mu1")),
    '[Datapoints, Mu] -> { [k, mu1] : 0 <= k < Datapoints && 0 <= mu1 < Mu }',
	op="sample"
)

cost_evaluator = PolyhedralCardExactCostEvaluator({'Datapoints': 10000, 'Mu': 10})

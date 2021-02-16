import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Datapoints", "Mu"]).params()

prog = Program(param_space)\
.add_stmt(
    "acc645__1", ["k", "mu1"],
    ConstExp(1),
    '[Datapoints, Mu] -> { [k, mu1, i] : 0 <= k < Datapoints && 0 <= mu1 < Mu && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("mu1"), "Mu")
    ]
).add_stmt(
	"z_new", ["k"],
	AccessExp("acc645__1", IdExp("k"), IdExp("mu1")),
    '[Datapoints, Mu] -> { [k, mu1] : 0 <= k < Datapoints && 0 <= mu1 < Mu }',
	op="sample"
)

cost_evaluator = PolyhedralCardExactCostEvaluator({'Datapoints': 10000, 'Mu': 10})

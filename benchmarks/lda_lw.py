import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Words", "Alphabet", "Topics", "Documents"]).params()

prog = Program(param_space)\
.add_stmt(
    "acc8_", ["k", "_ind6_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind6_, i] : 0 <= k < Words && 0 <= _ind6_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents")
    ]
).add_stmt(
    "acc9_", ["k", "_ind6_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind6_, i] : 0 <= k < Words && 0 <= _ind6_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents")
    ]
).add_stmt(
    "acc7_", ["k", "_ind6_"],
   OpExp("+", AccessExp("acc8_", IdExp("k"), IdExp("_ind6_")), AccessExp("acc9_", IdExp("k"), IdExp("_ind6_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind6_] : 0 <= k < Words && 0 <= _ind6_ < Topics }',
)\
\
.add_stmt(
    "z_new", ["k"],
    AccessExp("acc7_", IdExp("k"), IdExp("_ind6_")),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind6_] : 0 <= k < Words && 0 <= _ind6_ < Topics }',
    op="sample"
)\
\
.add_stmt(
    "acc13_", ["k", "_ind6_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind6_, i] : 0 <= k < Words && 0 <= _ind6_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("z_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc14_", ["k", "_ind6_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind6_, i] : 0 <= k < Words && 0 <= _ind6_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("z_new", IdExp("k")), "Topics"),
    ]
).add_stmt(
    "acc12_", ["k", "_ind6_"],
   OpExp("+", AccessExp("acc13_", IdExp("k"), IdExp("_ind6_")), AccessExp("acc14_", IdExp("k"), IdExp("_ind6_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind6_] : 0 <= k < Words && 0 <= _ind6_ < Topics }',
)

cost_evaluator = PolyhedralCardExactCostEvaluator({'Words': 466480, 'Alphabet': 6906, 'Topics': 50, 'Documents': 3430})

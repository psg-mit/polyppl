import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Words", "Alphabet", "Topics", "Documents"]).params()

prog = Program(param_space)\
.add_stmt(
    "acc7__1", ["k", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("_ind5_"), "Topics"),
        (AccessExp("w", IdExp("i")), AccessExp("w", IdExp("k")), "Alphabet"),
    ]
).add_stmt(
    "acc7__2", ["k", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("_ind5_"), "Topics"),
        (AccessExp("w", IdExp("i")), AccessExp("w", IdExp("k")), "Alphabet"),
    ]
).add_stmt(
    "acc7_", ["k", "_ind5_"],
    OpExp("+", AccessExp("acc7__1", IdExp("k"), IdExp("_ind5_")), AccessExp("acc7__2", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
).add_stmt(
    "acc6_", ["k", "_ind5_"],
    OpExp("f", AccessExp("acc7_", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
)\
\
.add_stmt(
    "acc11__1", ["k", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("_ind5_"), "Topics"),
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
    ]
).add_stmt(
    "acc11__2", ["k", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("_ind5_"), "Topics"),
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
    ]
).add_stmt(
    "acc11_", ["k", "_ind5_"],
    OpExp("+", AccessExp("acc11__1", IdExp("k"), IdExp("_ind5_")), AccessExp("acc11__2", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
).add_stmt(
    "acc10_", ["k", "_ind5_"],
    OpExp("f", AccessExp("acc11_", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
)\
\
\
\
\
.add_stmt(
    "acc18__1", ["k", "_ind5_", "_ind16_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("_ind16_"), "Topics"),
        (AccessExp("w", IdExp("i")), AccessExp("w", IdExp("k")), "Alphabet"),
    ]
).add_stmt(
    "acc18__2", ["k", "_ind5_", "_ind16_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("_ind16_"), "Topics"),
        (AccessExp("w", IdExp("i")), AccessExp("w", IdExp("k")), "Alphabet"),
    ]
).add_stmt(
    "acc18_", ["k", "_ind5_", "_ind16_"],
    OpExp("+", AccessExp("acc18__1", IdExp("k"), IdExp("_ind5_")), AccessExp("acc18__2", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics }',
).add_stmt(
    "acc17_", ["k", "_ind5_", "_ind16_"],
    OpExp("f", AccessExp("acc18_", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics }',
)\
\
.add_stmt(
    "acc22__1", ["k", "_ind5_", "_ind16_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), IdExp("_ind16_"), "Topics"),
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
    ]
).add_stmt(
    "acc22__2", ["k", "_ind5_", "_ind16_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_, i] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), IdExp("_ind16_"), "Topics"),
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
    ]
).add_stmt(
    "acc22_", ["k", "_ind5_", "_ind16_"],
    OpExp("+", AccessExp("acc22__1", IdExp("k"), IdExp("_ind5_")), AccessExp("acc22__2", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics }',
).add_stmt(
    "acc21_", ["k", "_ind5_", "_ind16_"],
    OpExp("f", AccessExp("acc22_", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics }',
)\
\
\
.add_stmt(
    "_ret15_", ["k", "_ind5_", "_ind16_"],
    OpExp("+", AccessExp("acc17_", IdExp("k"), IdExp("_ind5_"), IdExp("_ind16_")), AccessExp("acc21_", IdExp("k"), IdExp("_ind5_"), IdExp("_ind16_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics }',
)\
\
\
.add_stmt(
    "_ret15_logsum", ["k", "_ind5_"],
    AccessExp("_ret15_", IdExp("k"), IdExp("_ind5_"), IdExp("_ind16_")),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, _ind16_] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= _ind16_ < Topics }',
    op="logsumexp"
)\
\
\
.add_stmt(
    "_ret4_", ["k", "_ind5_"],
    OpExp("uninterpreted", AccessExp("acc6_", IdExp("k"), IdExp("_ind5_")), AccessExp("acc10_", IdExp("k"), IdExp("_ind5_")), AccessExp("_ret15_logsum", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
)\
\
\
.add_stmt(
    "z_new", ["k"],
     AccessExp("_ret4_", IdExp("k"), IdExp("_ind5_")),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
    op="sample"
)

cost_evaluator = PolyhedralCardExactCostEvaluator({'Words': 466480, 'Alphabet': 6906, 'Topics': 50, 'Documents': 3430})

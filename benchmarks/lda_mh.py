import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Words", "Alphabet", "Topics", "Documents"]).params()

prog = Program(param_space)\
.add_stmt(
    "acc7__1", ["k", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, w0] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= w0 < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("w0")), IdExp("_ind5_"), "Topics")
    ]
).add_stmt(
    "acc7__2", ["k", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, w0] : 0 <= k < Words && 0 <= _ind5_ < Topics && k < w0 < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("w0")), IdExp("_ind5_"), "Topics")
    ]
).add_stmt(
    "acc7_", ["k", "_ind5_"],
    OpExp("+", AccessExp("acc7__1", IdExp("k"), IdExp("_ind5_")), AccessExp("acc7__1", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
).add_stmt(
    "acc9_", ["k", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_, w0] : 0 <= k < Words && 0 <= _ind5_ < Topics && 0 <= w0 < Words && w0 != k }',
    op="+"
).add_stmt(
    "acc6_", ["k", "_ind5_"],
    OpExp("+", AccessExp("acc7_", IdExp("k"), IdExp("_ind5_")), AccessExp("acc9_", IdExp("k"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
).add_stmt(
    "q_new", ["k"],
   AccessExp("acc6_", IdExp("k"), IdExp("_ind5_")),
    '[Words, Alphabet, Topics, Documents] -> { [k, _ind5_] : 0 <= k < Words && 0 <= _ind5_ < Topics }',
    op="sample"
)\
\
\
.add_stmt(
    "acc11__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, w0] : 0 <= k < Words && 0 <= w0 < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("w0")), AccessExp("q_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc11__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, w0] : 0 <= k < Words && k < w0 < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("w0")), AccessExp("q_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc11_", ["k"],
    OpExp("+", AccessExp("acc11__1", IdExp("k")), AccessExp("acc11__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc13_", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, w0] : 0 <= k < Words && 0 <= w0 < Words && w0 != k }',
    op="+"
).add_stmt(
    "acc10_", ["k"],
    OpExp("+", AccessExp("acc11_", IdExp("k")), AccessExp("acc13_", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc15__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("q_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc15__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("q_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc15_", ["k"],
    OpExp("+", AccessExp("acc15__1", IdExp("k")), AccessExp("acc15__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc17__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 <= i < k}',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("q_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc17__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("q_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc17_", ["k"],
    OpExp("+", AccessExp("acc17__1", IdExp("k")), AccessExp("acc17__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc14_", ["k"],
    OpExp("f", AccessExp("acc15_", IdExp("k")), AccessExp("acc17_", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc19__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc19__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc19_", ["k"],
    OpExp("+", AccessExp("acc19__1", IdExp("k")), AccessExp("acc19__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc21_", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 < i < Words && i != k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents")
    ]
).add_stmt(
    "acc18_", ["k"],
    OpExp("+", AccessExp("acc19_", IdExp("k")), AccessExp("acc21_", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc24__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, w0] : 0 <= k < Words && 0 <= w0 < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("w0")), AccessExp("z_old", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc24__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, w0] : 0 <= k < Words && k < w0 < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("w0")), AccessExp("z_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc24_", ["k"],
   OpExp("+", AccessExp("acc24__1", IdExp("k")), AccessExp("acc24__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc26_", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, w0] : 0 <= k < Words && 0 <= w0 < Words && w0 != k }',
    op="+"
).add_stmt(
    "acc23_", ["k"],
    OpExp("+", AccessExp("acc24_", IdExp("k")), AccessExp("acc26_", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc27__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc27__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("q_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc27_", ["k"],
    OpExp("+", AccessExp("acc27__1", IdExp("k")), AccessExp("acc27__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc30__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 <= i < k}',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc30__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("z_new", IdExp("i")), AccessExp("z_new", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc30_", ["k"],
    OpExp("+", AccessExp("acc30__1", IdExp("k")), AccessExp("acc30__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc27_", ["k"],
    OpExp("+", AccessExp("acc27_", IdExp("k")), AccessExp("acc30_", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc32__1", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 <= i < k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc32__2", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && k < i < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents"),
        (AccessExp("z_old", IdExp("i")), AccessExp("z_old", IdExp("k")), "Topics")
    ]
).add_stmt(
    "acc32_", ["k"],
    OpExp("+", AccessExp("acc32__1", IdExp("k")), AccessExp("acc32__1", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "acc34_", ["k"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [k, i] : 0 <= k < Words && 0 < i < Words && i != k }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("k")), "Documents")
    ]
).add_stmt(
    "acc31_", ["k"],
    OpExp("+", AccessExp("acc32_", IdExp("k")), AccessExp("acc34_", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }',
).add_stmt(
    "ret_22", ["k"],
    OpExp("f", AccessExp("acc23_", IdExp("k")), AccessExp("acc27_", IdExp("k")), AccessExp("acc31_", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }'
).add_stmt(
    "z_new", ["k"],
    OpExp("f", AccessExp("acc10_", IdExp("k")), AccessExp("acc14_", IdExp("k")), AccessExp("acc18_", IdExp("k")), AccessExp("ret_22", IdExp("k"))),
    '[Words, Alphabet, Topics, Documents] -> { [k] : 0 <= k < Words }'
)

cost_evaluator = PolyhedralCardExactCostEvaluator({'Words': 466480, 'Alphabet': 6906, 'Topics': 50, 'Documents': 3430})

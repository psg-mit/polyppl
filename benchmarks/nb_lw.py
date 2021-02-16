import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Words", "Alphabet", "Topics", "Documents"]).params()

prog = Program(param_space)\
.add_stmt(
    'acc10_', ['notd', '_ind8_'],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [notd, _ind8_, d] : 0 <= notd < Documents && 0 <= _ind8_ < Topics &&  0 <= d < notd }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", IdExp("d")), IdExp("_ind8_"), "Topics")
    ]
).add_stmt(
    'acc12_', ['notd', '_ind8_'],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [notd, _ind8_, d] : 0 <= notd < Documents && 0 <= _ind8_ < Topics &&  0 <= d < Documents && d != notd }',
    op="+"
).add_stmt(
    'acc9_', ['notd', '_ind8_'],
    OpExp("f", AccessExp("acc10_", IdExp("notd"), IdExp("_ind8_")), AccessExp("acc12_", IdExp("notd"), IdExp("_ind8_"))),
    '[Words, Alphabet, Topics, Documents] -> { [notd, _ind8_] : 0 <= notd < Documents && 0 <= _ind8_ < Topics }'
).add_stmt(
    "label_new", ['notd'],
    AccessExp("acc9_", IdExp("notd"), IdExp("_ind8_")),
    '[Words, Alphabet, Topics, Documents] -> { [notd, _ind8_] : 0 <= notd < Documents && 0 <= _ind8_ < Topics }',
    op="sample"
)\
.add_stmt(
    "acc14_", ["notd"],
    OpExp("catd", AccessExp("words", IdExp("w")), AccessExp("theta", AccessExp("label_new", IdExp("notd")))),
    '[Words, Alphabet, Topics, Documents] -> { [notd, w] : 0 <= notd < Documents && 0 <= w < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("notd"), "Documents")
    ]
)\
.add_stmt(
    "acc15_", ["notd", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("notd"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [notd, a0, w] : 0 <= notd < Documents && 0 <= a0 < Alphabet && 0 <= w < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), AccessExp("label_new", IdExp("notd")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
)\
.add_stmt(
    "acc17_", ["notd", "a0"],
    OpExp("f<=", AccessExp("docMap", IdExp("w")), IdExp("notd"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [notd, a0, w] : 0 <= notd < Documents && 0 <= a0 < Alphabet && 0 <= w < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), AccessExp("label_new", IdExp("notd")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
)\
.add_stmt(
    "acc15_sample", ["notd"],
    AccessExp("acc15_", IdExp("notd"), IdExp("a0")),
    '[Words, Alphabet, Topics, Documents] -> { [notd, a0] : 0 <= notd < Documents && 0 <= a0 < Alphabet }',
    op="sample_dir"
)\
.add_stmt(
    "acc17_sample", ["notd"],
    AccessExp("acc17_", IdExp("notd"), IdExp("a0")),
    '[Words, Alphabet, Topics, Documents] -> { [notd, a0] : 0 <= notd < Documents && 0 <= a0 < Alphabet }',
    op="sample_dir"
)\
.add_stmt(
    "acc13_", ["notd"],
    OpExp("f", AccessExp("acc14_", IdExp("notd")), AccessExp("acc15_", IdExp("notd")), AccessExp("acc17_", IdExp("notd"))),
    '[Words, Alphabet, Topics, Documents] -> { [notd] : 0 <= notd < Documents }'
)


cost_evaluator = PolyhedralCardExactCostEvaluator({'Topics': 4, 'Documents': 280, 'Alphabet': 129, "Words": 569800})

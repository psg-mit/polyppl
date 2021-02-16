import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Words", "Alphabet", "Topics", "Documents"]).params()

prog = Program(param_space)\
.add_stmt(
    "acc8_", ["di", "_ind7_"],
    OpExp("catd", AccessExp("words", IdExp("w")), AccessExp("theta", IdExp("_ind7_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= w < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents")
    ]
)\
.add_stmt(
    "acc10__1", ["di", "_ind7_", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), IdExp("_ind7_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc10__2", ["di", "_ind7_", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), IdExp("_ind7_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc10_", ["di", "_ind7_", "a0"],
    OpExp("+", AccessExp("acc10__1", IdExp("di"), IdExp("_ind7_"), IdExp("a0")), AccessExp("acc10__2", IdExp("di"), IdExp("_ind7_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc9_", ["di", "_ind7_", "a0"],
    OpExp("f", AccessExp("acc10_", IdExp("di"), IdExp("_ind7_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= a0 < Alphabet }',
)\
.add_stmt(
    "acc12__1", ["di", "_ind7_", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), IdExp("_ind7_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc12__2", ["di", "_ind7_", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), IdExp("_ind7_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc12__3", ["di", "_ind7_", "a0"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc12_", ["di", "_ind7_", "a0"],
    OpExp("+", AccessExp("acc12__1", IdExp("di"), IdExp("_ind7_"), IdExp("a0")), AccessExp("acc12__2", IdExp("di"), IdExp("_ind7_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc11_", ["di", "_ind7_", "a0"],
    OpExp("f", AccessExp("acc12_", IdExp("di"), IdExp("_ind7_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= a0 < Alphabet }',
)\
.add_stmt(
    "acc14__1", ["di", "_ind7_"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, d] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= d < di }',
    non_affine_constraints=[
        (AccessExp("label_old", IdExp("d")), IdExp("_ind7_"), "Topics"),
    ],
    op="+"
).add_stmt(
    "acc14__2", ["di", "_ind7_"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, d] : 0 <= di < Documents && 0 <= _ind7_ < Topics && di < d < Documents }',
    non_affine_constraints=[
        (AccessExp("label_new", IdExp("d")), IdExp("_ind7_"), "Topics"),
    ],
    op="+"
).add_stmt(
    "acc14_", ["di", "_ind7_"],
    OpExp("+", AccessExp("acc14__1", IdExp("di"), IdExp("_ind7_")), AccessExp("acc14__2", IdExp("di"), IdExp("_ind7_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_] : 0 <= di < Documents && 0 <= _ind7_ < Topics }',
).add_stmt(
    "acc16_", ["di", "_ind7_"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, d] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= d < Documents && d != di }',
    op="+"
).add_stmt(
    "acc13_", ["di", "_ind7_"],
    OpExp("f", AccessExp("acc14_", IdExp("di"), IdExp("_ind7_")), AccessExp("acc16_", IdExp("di"), IdExp("_ind7_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_] : 0 <= di < Documents && 0 <= _ind7_ < Topics }'
)\
\
\
.add_stmt(
    "acc20_", ["di", "_ind7_", "_ind19_"],
    OpExp("catd", AccessExp("words", IdExp("w")), AccessExp("theta", IdExp("_ind19_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= w < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents")
    ]
)\
.add_stmt(
    "acc22__1", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), IdExp("_ind19_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc22__2", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), IdExp("_ind19_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc22_", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("+", AccessExp("acc22__1", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0")), AccessExp("acc22__2", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc21_", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("f", AccessExp("acc22_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= a0 < Alphabet }',
)\
.add_stmt(
    "acc24__1", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), IdExp("_ind19_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc24__2", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), IdExp("_ind19_"), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc24__3", ["di", "_ind7_", "_ind19_", "a0"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0, w] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc24_", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("+", AccessExp("acc24__1", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0")), AccessExp("acc24__2", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc23_", ["di", "_ind7_", "_ind19_", "a0"],
    OpExp("f", AccessExp("acc24_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= a0 < Alphabet }',
)\
.add_stmt(
    "acc26__1", ["di", "_ind7_", "_ind19_"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, d] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= d < di }',
    non_affine_constraints=[
        (AccessExp("label_old", IdExp("d")), IdExp("_ind19_"), "Topics"),
    ],
    op="+"
).add_stmt(
    "acc26__2", ["di", "_ind7_", "_ind19_"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, d] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && di < d < Documents }',
    non_affine_constraints=[
        (AccessExp("label_new", IdExp("d")), IdExp("_ind19_"), "Topics"),
    ],
    op="+"
).add_stmt(
    "acc26_", ["di", "_ind7_", "_ind19_"],
    OpExp("+", AccessExp("acc26__1", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_")), AccessExp("acc26__2", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics }',
).add_stmt(
    "acc28_", ["di", "_ind7_", "_ind19_"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, d] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= d < Documents && d != di }',
    op="+"
).add_stmt(
    "acc25_", ["di", "_ind7_", "_ind19_"],
    OpExp("f", AccessExp("acc26_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_")), AccessExp("acc28_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics }'
)\
.add_stmt(
    "acc21_sample", ["di", "_ind7_", "_ind19_"],
    OpExp(AccessExp("theta", IdExp("_ind19_")), AccessExp("acc21_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= a0 < Alphabet}',
    op="sample"
)\
.add_stmt(
    "acc23_sample", ["di", "_ind7_", "_ind19_"],
    OpExp(AccessExp("theta", IdExp("_ind19_")), AccessExp("acc23_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= a0 < Alphabet}',
    op="sample"
).add_stmt(
    "acc25_sample", ["di", "_ind7_", "_ind19_"],
    OpExp(AccessExp("theta", IdExp("_ind19_")), AccessExp("acc25_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics && 0 <= a0 < Alphabet}',
    op="sample"
).add_stmt(
    "_ret18_", ["di", "_ind7_", "_ind19_"],
    OpExp("f", AccessExp("acc20_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_")), AccessExp("acc21_sample", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_")), AccessExp("acc23_sample", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_")),  AccessExp("acc25_sample", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics }',
)\
.add_stmt(
    "acc9_sample", ["di", "_ind7_"],
    OpExp(AccessExp("theta", IdExp("_ind19_")), AccessExp("acc9_", IdExp("di"), IdExp("_ind7_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= a0 < Alphabet}',
    op="sample"
)\
.add_stmt(
    "acc11_sample", ["di", "_ind7_"],
    OpExp(AccessExp("theta", IdExp("_ind19_")), AccessExp("acc11_", IdExp("di"), IdExp("_ind7_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= a0 < Alphabet}',
    op="sample"
).add_stmt(
    "acc13_sample", ["di", "_ind7_"],
    OpExp(AccessExp("theta", IdExp("_ind19_")), AccessExp("acc13_", IdExp("di"), IdExp("_ind7_"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, a0] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= a0 < Alphabet}',
    op="sample"
).add_stmt(
    "_ret18_logsum", ["di", "_ind7_"],
    AccessExp("_ret18_", IdExp("di"), IdExp("_ind7_"), IdExp("_ind19_")),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_, _ind19_] : 0 <= di < Documents && 0 <= _ind7_ < Topics && 0 <= _ind19_ < Topics }',
    op="logsum"
)\
.add_stmt(
    "_ret6_", ["di", "_ind7_"],
    OpExp("f", AccessExp("acc8_", IdExp("di"), IdExp("_ind7_")), AccessExp("acc9_sample", IdExp("di"), IdExp("_ind7_")),  AccessExp("acc11_sample", IdExp("di"), IdExp("_ind7_")), AccessExp("acc13_sample", IdExp("di"), IdExp("_ind7_")), AccessExp("_ret18_logsum", IdExp("di"), IdExp("_ind7_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_] : 0 <= di < Documents && 0 <= _ind7_ < Topics }',
)\
.add_stmt(
    "label_new'", ["di"],
    AccessExp("_ret6_", IdExp("di"), IdExp("_ind7_")),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind7_] : 0 <= di < Documents && 0 <= _ind7_ < Topics }',
    op="sample"
)


cost_evaluator = PolyhedralCardExactCostEvaluator({'Topics': 4, 'Documents': 280, 'Alphabet': 129, "Words": 569800})

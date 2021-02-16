import islpy
from optimization.polyast import *
from optimization.search import DEFAULT_COST_EVALUTATOR, PolyhedralCardExactCostEvaluator

ctx = islpy.Context()

param_space = islpy.Space.create_from_names(ctx, in_=[], out=[], params=["Words", "Alphabet", "Topics", "Documents"]).params()

prog = Program(param_space)\
.add_stmt(
    "acc9__1", ["di", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind5_, d0] : 0 <= di < Documents && 0 <= _ind5_ < Topics && 0 <= d0 < di }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", IdExp("d0")), IdExp("_ind5_"), "Topics")
    ]
).add_stmt(
    "acc9__2", ["di", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind5_, d0] : 0 <= di < Documents && 0 <= _ind5_ < Topics && di < d0 < Documents }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", IdExp("d0")), IdExp("_ind5_"), "Topics")
    ]
).add_stmt(
    "acc9_", ["di", "_ind5_"],
    OpExp("+", AccessExp("acc9__1", IdExp("di"), IdExp("_ind5_")), AccessExp("acc9__1", IdExp("di"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind5_] : 0 <= di < Documents && 0 <= _ind5_ < Topics }',
).add_stmt(
    "acc9_", ["di", "_ind5_"],
   ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind5_, d0] : 0 <= di < Documents && 0 <= _ind5_ < Topics && 0 <= d0 < Documents && d0 != di }',
    op="+"
).add_stmt(
    "acc8_", ["di", "_ind5_"],
    OpExp("+", AccessExp("acc9_", IdExp("di"), IdExp("_ind5_")), AccessExp("acc9_", IdExp("di"), IdExp("_ind5_"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind5_] : 0 <= di < Documents && 0 <= _ind5_ < Topics }',
).add_stmt(
    "q_new", ["di"],
   AccessExp("acc8_", IdExp("di"), IdExp("_ind5_")),
    '[Words, Alphabet, Topics, Documents] -> { [di, _ind5_] : 0 <= di < Documents && 0 <= _ind5_ < Topics }',
    op="sample"
)\
\
\
.add_stmt(
    "acc13__1", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, d0] : 0 <= di < Documents && 0 <= d0 < di }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", IdExp("d0")), AccessExp("q_new", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc13__2", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, d0] : 0 <= di < Documents && di < d0 < Documents }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", IdExp("d0")), AccessExp("q_new", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc13_", ["di"],
    OpExp("+", AccessExp("acc13__1", IdExp("di")), AccessExp("acc13__1", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
).add_stmt(
    "acc15_", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, d0] : 0 <= di < Documents && 0 <= d0 < Documents && d0 != di }',
    op="+"
).add_stmt(
    "acc12_", ["di"],
    OpExp("+", AccessExp("acc13_", IdExp("di")), AccessExp("acc15_", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
)\
\
.add_stmt(
    "acc16_", ["di"],
    OpExp("catd", AccessExp("words", IdExp("w")), AccessExp("theta", AccessExp("q", IdExp("di")))),
    '[Words, Alphabet, Topics, Documents] -> { [di, w] : 0 <= di < Documents && 0 <= w < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents"),
    ]
)\
\
.add_stmt(
    "acc18__1", ["di", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), AccessExp("q_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc18__2", ["di", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), AccessExp("q_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc18_", ["di", "a0"],
    OpExp("+", AccessExp("acc18__1", IdExp("di"), IdExp("a0")), AccessExp("acc18__2", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc17_", ["di", "a0"],
    OpExp("f", AccessExp("acc18_", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
)\
\
.add_stmt(
    "acc20__1", ["di", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), AccessExp("q_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc20__2", ["di", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), AccessExp("q_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc20__3", ["di", "a0"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc20_", ["di", "a0"],
    OpExp("+", AccessExp("acc20__1", IdExp("di"), IdExp("a0")), AccessExp("acc20__2", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc19_", ["di", "a0"],
    OpExp("f", AccessExp("acc20_", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
)\
\
.add_stmt(
    "acc22__1", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, i] : 0 <= di < Documents && 0 <= i < di }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("di")), "Documents"),
        (AccessExp("label_old", IdExp("i")), AccessExp("label_old", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc22__2", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, i] : 0 <= di < Documents && di < i < Documents }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("di")), "Documents"),
        (AccessExp("label_old", IdExp("i")), AccessExp("label_old", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc22_", ["di"],
    OpExp("+", AccessExp("acc22__1", IdExp("di")), AccessExp("acc22__1", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
).add_stmt(
    "acc24_", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, i] : 0 <= di < Documents && 0 < i < Documents && i != di }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("di")), "Documents")
    ]
).add_stmt(
    "acc21_", ["di"],
    OpExp("+", AccessExp("acc22_", IdExp("di")), AccessExp("acc24_", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
)\
\
.add_stmt(
    "acc27__1", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, d0] : 0 <= di < Documents && 0 <= d0 < di }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", IdExp("d0")), AccessExp("label_old", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc27__2", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, d0] : 0 <= di < Documents && di < d0 < Documents }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", IdExp("d0")), AccessExp("label_new", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc27_", ["di"],
    OpExp("+", AccessExp("acc27__1", IdExp("di")), AccessExp("acc27__1", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
).add_stmt(
    "acc15_", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, d0] : 0 <= di < Documents && 0 <= d0 < Documents && d0 != di }',
    op="+"
).add_stmt(
    "acc26_", ["di"],
    OpExp("+", AccessExp("acc27_", IdExp("di")), AccessExp("acc15_", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
)\
\
.add_stmt(
    "acc30_", ["di"],
    OpExp("catd", AccessExp("words", IdExp("w")), AccessExp("theta", AccessExp("q", IdExp("di")))),
    '[Words, Alphabet, Topics, Documents] -> { [di, w] : 0 <= di < Documents && 0 <= w < Words }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents"),
    ]
)\
\
.add_stmt(
    "acc32__1", ["di", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), AccessExp("label_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc32__2", ["di", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), AccessExp("label_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc32_", ["di", "a0"],
    OpExp("+", AccessExp("acc32__1", IdExp("di"), IdExp("a0")), AccessExp("acc32__2", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc31_", ["di", "a0"],
    OpExp("f", AccessExp("acc32_", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
)\
\
.add_stmt(
    "acc34__1", ["di", "a0"],
    OpExp("f<", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_old", AccessExp("docMap", IdExp("w"))), AccessExp("label_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc34__2", ["di", "a0"],
    OpExp("f>", AccessExp("docMap", IdExp("w")), IdExp("di"), ConstExp(1)),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("label_new", AccessExp("docMap", IdExp("w"))), AccessExp("label_new", IdExp("di")), "Topics"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc34__3", ["di", "a0"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0, w] : 0 <= di < Documents && 0 <= w < Words && 0 <= a0 < Alphabet }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("w")), IdExp("di"), "Documents"),
        (AccessExp("words", IdExp("w")), IdExp("a0"), "Alphabet")
    ]
).add_stmt(
    "acc34_", ["di", "a0"],
    OpExp("+", AccessExp("acc34__1", IdExp("di"), IdExp("a0")), AccessExp("acc34__2", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
).add_stmt(
    "acc19_", ["di", "a0"],
    OpExp("f", AccessExp("acc34_", IdExp("di"), IdExp("a0"))),
    '[Words, Alphabet, Topics, Documents] -> { [di, a0] : 0 <= di < Documents && 0 <= a0 < Alphabet }',
)\
\
.add_stmt(
    "acc36__1", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, i] : 0 <= di < Documents && 0 <= i < di }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("di")), "Documents"),
        (AccessExp("label_old", IdExp("i")), AccessExp("label_old", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc36__2", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, i] : 0 <= di < Documents && di < i < Documents }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("di")), "Documents"),
        (AccessExp("label_old", IdExp("i")), AccessExp("label_old", IdExp("di")), "Topics")
    ]
).add_stmt(
    "acc36_", ["di"],
    OpExp("+", AccessExp("acc36__1", IdExp("di")), AccessExp("acc36__1", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
).add_stmt(
    "acc38_", ["di"],
    ConstExp(1),
    '[Words, Alphabet, Topics, Documents] -> { [di, i] : 0 <= di < Documents && 0 < i < Documents && i != di }',
    op="+",
    non_affine_constraints=[
        (AccessExp("docMap", IdExp("i")), AccessExp("docMap", IdExp("di")), "Documents")
    ]
).add_stmt(
    "acc35_", ["di"],
    OpExp("+", AccessExp("acc36_", IdExp("di")), AccessExp("acc38_", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }',
)\
.add_stmt(
    "ret_22", ["di"],
    OpExp("f", AccessExp("q_new", IdExp("di")), AccessExp("theta", AccessExp("label_old", IdExp("di"))), AccessExp("acc26_", IdExp("di")), AccessExp("acc30_", IdExp("di")), AccessExp("acc31_", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }'
).add_stmt(
    "z_new", ["di"],
    OpExp("f", AccessExp("q_new", IdExp("di")), AccessExp("theta", AccessExp("label_old", IdExp("di"))), AccessExp("acc26_", IdExp("di")), AccessExp("acc30_", IdExp("di")), AccessExp("acc31_", IdExp("di")), AccessExp("ret_22", IdExp("di"))),
    '[Words, Alphabet, Topics, Documents] -> { [di] : 0 <= di < Documents }'
)

cost_evaluator = PolyhedralCardExactCostEvaluator({'Topics': 4, 'Documents': 280, 'Alphabet': 129, "Words": 569800})

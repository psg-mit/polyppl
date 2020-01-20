import islpy
ctx = islpy.Context()
schedule_map = islpy.UnionMap.read_from_str(
    ctx, "[N] -> { S0[i] -> [N-i, 0] : 0 <= i < N; }")
ast_build = islpy.AstBuild.from_context(
    islpy.Set.read_from_str(ctx, "[N] -> { : }"))
ast = ast_build.node_from_schedule_map(schedule_map)

print(ast.to_C_str())
# Prints below code:
# for (int c0 = 0; c0 < N; c0 += 1) {
#  S0(c0);
#  S1(c0);
# }

# we have S0 and S1 in a ast_node_block
body = ast.for_get_body()
assert body.get_type() == islpy.ast_node_type.block

# body.block_get_children()
# Raises exception!

using PCT, GraphPlot, Graphs

f, ctx = @pct begin
    @space M begin
        type=(I, I) -> C
    end

    (A, i::I, j::I) -> _
end

g_1 = @pct f ctx i * A(i, j)
g_2 = @pct f ctx j * A(j, i)

i_tree = SignatureTree(Var(I(), :i), fc(g_1), [Var(I(), :j)])
j_tree = SignatureTree(Var(I(), :j), fc(g_2), [Var(I(), :i)])
other_tree = SignatureTree(Var(I(), :i), fc(g_2), [Var(I(), :j)])

hash(i_tree)
hash(j_tree)

i_tree == i_tree
i_tree == j_tree
i_tree == other_tree
j_tree == other_tree

node_label(::Type{PCTVector}, ::Nothing) = "[]"
node_label(::Type{PrimitiveCall}, ::Nothing) = "Call"
node_label(::Type{T}, ::Nothing) where T <: Var = "Var"
node_label(::Type{T}, v::S) where {T <: Var, S <: Var} = string(v.content)
node_label(::Type{T}, ::Nothing) where T <: APN = string(T)

nodes, edges = tree_dfs_vis(i_tree)
g = SimpleDiGraph(Edge.(edges))
gplothtml(g, nodelabel=["$(node_label(n, e)): $(i)" for ((n, e), i) in nodes])

# nodes, edges = tree_dfs_vis(j_tree)
# g = SimpleDiGraph(Edge.(edges))
# gplothtml(g, nodelabel=["$(node_label(n, e)): $(i)" for ((n, e), i) in nodes])


g_1 = @pct f ctx i * (A(i, j) + A(j, i))
i_tree = SignatureTree(Var(I(), :i), fc(g_1), [Var(I(), :j)])
nodes, edges = tree_dfs_vis(i_tree)
g = SimpleDiGraph(Edge.(edges))
gplothtml(g, nodelabel=["$(node_label(n, e)): $(i)" for ((n, e), i) in nodes])

x = @pct f ctx sum((i, j), A(i, j))
y = @pct f ctx sum((j, i), A(j, i))
x == x
x == y


# g_1 = @pct f ctx i * A(i, j)
# i_tree_1 = SignatureTree(Var(I(), :i), fc(g_1))
# i_tree_2 = SignatureTree(Var(I(), :i), fc(@pct f ctx i * A(j, i)))
# i_tree_1 == i_tree_2

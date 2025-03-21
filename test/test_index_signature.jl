using CombDiff

function graphical_test()
    g_1 = get_body(first(@main (A::M, i::N, j::N) -> i * A(i, j) _ ctx))
    i_tree = SignatureTree(var(:i, N()), get_body(g_1), [var(:j, N())])
    nodes, edges = tree_dfs_vis(i_tree)
    g = SimpleDiGraph(Edge.(edges))
    gplothtml(g, nodelabel=["$(node_label(n, e)): $(i)" for ((n, e), i) in nodes])
    node_label(::Type{PCTVector}, ::Nothing) = "[]"
    node_label(::Type{PrimitiveCall}, ::Nothing) = "Call"
    node_label(::Type{T}, ::Nothing) where {T<:Var} = "Var"
    node_label(::Type{T}, v::S) where {T<:Var,S<:Var} = string(v.content)
    node_label(::Type{T}, ::Nothing) where {T<:APN} = string(T)

    nodes, edges = tree_dfs_vis(i_tree)
    g = SimpleDiGraph(Edge.(edges))
    gplothtml(g, nodelabel=["$(node_label(n, e)): $(i)" for ((n, e), i) in nodes])
end

@testset "index_sig: equivalence" begin
    _, ctx = @comb begin
        @space M begin
            type = (N, N) -> C
            symmetries = (A -> (i, j) -> A(j, i),)
        end
    end

    g_1 = get_body(first(@main (A::M, i::N, j::N) -> i * A(i, j) _ ctx))
    g_2 = get_body(first(@main (A::M, i::N, j::N) -> j * A(j, i) _ ctx))

    i_tree = SignatureTree(var(:i, N()), get_body(g_1), [var(:j, N())])
    j_tree = SignatureTree(var(:j, N()), get_body(g_2), [var(:i, N())])
    other_tree = SignatureTree(var(:i, N()), get_body(g_2), [var(:j, N())])

    @test hash(i_tree) == hash(j_tree)

    @test i_tree == i_tree
    @test i_tree == j_tree
    @test i_tree != other_tree
    @test j_tree != other_tree

    x = get_body(first(@main (A::M) -> sum((i, j), A(i, j)) _ ctx))
    y = get_body(first(@main (A::M) -> sum((j, i), A(j, i)) _ ctx))
    @test x == x
    @test x == y
end







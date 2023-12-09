using PCT, GraphPlot, Graphs

function graphical_test()
    g_1 = @pct f ctx i * (A(i, j) + A(j, i))
    i_tree = SignatureTree(Var(I(), :i), fc(g_1), [Var(I(), :j)])
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
    f, ctx = @pct begin
        @space M begin
            type = (I, I) -> C
            symmetries=(((2, 1), :id), )
        end

        (A, i::I, j::I) -> _
    end

    g_1 = @pct f ctx i * A(i, j)
    g_2 = @pct f ctx j * A(j, i)

    i_tree = SignatureTree(var(:i, I()), fc(g_1), [var(:j, I())])
    j_tree = SignatureTree(var(:j, I()), fc(g_2), [var(:i, I())])
    other_tree = SignatureTree(var(:i, I()), fc(g_2), [var(:j, I())])

    @test hash(i_tree) == hash(j_tree)

    @test i_tree == i_tree
    @test i_tree == j_tree
    @test i_tree != other_tree
    @test j_tree != other_tree

    x = @pct f ctx sum((i, j), A(i, j))
    y = @pct f ctx sum((j, i), A(j, i))
    @test x == x
    @test x == y
end







using GraphPlot

export PCTGraph, nodes, edges, spanning_tree!, graphs_jl, visualize, simplify

struct PCTGraph
    nodes::Vector
    edges::Vector
end

nodes(g::PCTGraph) = g.nodes
edges(g::PCTGraph) = g.edges

function pretty(g::PCTGraph)
    join(pretty.(nodes(g)), ";\n")
end

function Base.show(io::IO, ::MIME"text/plain", g::PCTGraph)
    print(io, pretty(g))
end

PCTGraph() = PCTGraph(Vector{APN}(), Vector{Pair{Int, Int}}())
    

function PCTGraph(n::APN) 
    g = PCTGraph(Vector{APN}(), Vector{Pair{Int, Int}}())
    push!(nodes(g), n)
    return g
end

#= function spanning_tree!(n::APN, g=PCTGraph(n))

    neighbor_list = neighbors(n)
    #= neighbor_list = filter(((t, d), )->!(t in nodes(g)), collect(zip(nodes(neighbor_list), directed(neighbor_list)))) =#
    #= index_n = findfirst(t->t==n, nodes(g)) =#
    index_n = length(nodes(g))

    for (t, d) in zip(nodes(neighbor_list), directed(neighbor_list))
        #= !d && push!(edges(g), length(nodes(g))=>index_n) =#

        if d
            println("Directed!")
            println("N:", pretty(n))
            println()
            (tree, _) = spanning_tree!(t, g)
            #= println()
            println("tree:", length(nodes(tree)))
            println("t:", pretty(t)) =#
            return (tree, true)
        else
            t in nodes(g) && continue
            println("Undirected?")
            push!(nodes(g), t)
            push!(edges(g), index_n=>length(nodes(g)))
            push!(edges(g), length(nodes(g))=>index_n) 
            (tree, d) = spanning_tree!(t, g)
            d && return (tree, d)
        end
    end

    #= for (t, _) in neighbor_list
        spanning_tree!(t, g)
    end =#
    #= println(pretty(g)) =#

    return (g, false)
end =#

"""

If there is a sink cluster: return the sink cluster with a `true`.
If there is no sink cluster: traverse the subgraph and 
    1. add the subgraph to seen.
    2. return the subgraph.

"""
function spanning_tree!(n::APN, seen=PCTGraph())
    push!(nodes(seen), n)
    node_start, edge_start = (length(nodes(seen)), length(edges(seen)))
    neighbor_list = neighbors(n)
    #= for (t, d, name) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        println("$(name): $(pretty(t))")
        println(d)
    end
    println() =#
    node_and_dir = collect(zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list)))
    neighbor_list = filter(((t, d, name), )->!(t in nodes(seen)), node_and_dir)

    for (t, d, _) in neighbor_list
        push!(edges(seen), node_start=>1+length(nodes(seen)))
        !d && push!(edges(seen), 1+length(nodes(seen))=>node_start)
        sink, tree = spanning_tree!(t, seen)
        (d || sink) && return (true, tree)
    end

    new_nodes = nodes(seen)[node_start:end]
    new_edges = edge_start == length(edges(seen)) ? Vector{Pair{Int, Int}}() : edges(seen)[edge_start:end]
    return false, PCTGraph(new_nodes, new_edges)
end



function simplify(n::APN)
    g = last(spanning_tree!(n))
    min_size = minimum(pct_size, nodes(g))
    return filter(t->pct_size(t)==min_size, nodes(g))
end

function simplify(n::Map)
    map(t->make_node!(Map, ff(n), t), simplify(fc(n)))
end


function graphs_jl(g::PCTGraph)
    SimpleDiGraph(Edge.(edges(g)))
end

function visualize(g::PCTGraph)
    h = graphs_jl(g)
    label(n::APN) = "$(pretty(n))\n$(pct_size(n))"
    gplothtml(h, nodesize=fill(80, length(nodes(g))), nodelabel=label.(nodes(g)))
end


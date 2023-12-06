using GraphPlot, DataStructures

export PCTGraph, nodes, edges, spanning_tree!, graphs_jl, visualize, simplify

struct PCTGraph
    nodes::Vector{APN}
    edges::Vector{Pair{Int, Int}}
    hashset::RBTree{APN}
end

nodes(g::PCTGraph) = g.nodes
edges(g::PCTGraph) = g.edges
hashset(g::PCTGraph) = g.hashset

function pretty(g::PCTGraph)
    join(pretty.(nodes(g)), ";\n")
end

function Base.show(io::IO, ::MIME"text/plain", g::PCTGraph)
    print(io, pretty(g))
end

PCTGraph() = PCTGraph(Vector{APN}(), Vector{Pair{Int, Int}}(), RBTree{APN}())
    

function PCTGraph(n::APN) 
    g = PCTGraph(Vector{APN}(), Vector{Pair{Int, Int}}(), RBTree{APN}())
    push!(nodes(g), n)
    push!(hashset(g), n)
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
function spanning_tree!(n::APN, seen=PCTGraph(); settings=Dict{Symbol, Bool}())
    push!(nodes(seen), n)
    #= println("pushing $(hashset(seen))") =#
    push!(hashset(seen), n)
    node_start, edge_start = (length(nodes(seen)), length(edges(seen)))
    neighbor_list = neighbors(n; settings=settings)
    #= for (t, d, name) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        println("$(name): $(pretty(t))")
        println(d)
    end
    println() =#

    #= println("num neighbors: $(length(neighbor_list))") =#
    reduced_list = Vector{Tuple{APN, Bool, String}}()
    @time for (t, d, name) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        t in hashset(seen) || push!(reduced_list, (t, d, name))
    end
    
    for (t, d, name) in sort(reduced_list, by=e->-e[2])
        push!(edges(seen), node_start=>1+length(nodes(seen)))
        !d && push!(edges(seen), 1+length(nodes(seen))=>node_start)
        println(length(nodes(seen)), " ", name, )
        println(pretty(n))
        println(pretty(t))
        d || println("notdirected")
        d && println("yesdirected!")
        println()
        sink, tree = spanning_tree!(t, seen; settings=settings)
        (d || sink) && return (true, tree)
    end

    new_nodes = nodes(seen)[node_start:end]
    new_edges = edge_start == length(edges(seen)) ? Vector{Pair{Int, Int}}() : edges(seen)[edge_start+1:end]
    return false, PCTGraph(new_nodes, new_edges, hashset(seen))
    #= return false, PCTGraph(new_nodes, new_edges, Set(new_nodes)) =#
end



function simplify(n::APN; settings=Dict{Symbol, Bool}())
    g = last(spanning_tree!(n; settings=settings))
    min_size = minimum(pct_size, nodes(g))
    smallest = Vector{APN}()

    for n in nodes(g)
        pct_size(n) == min_size && push!(smallest, n)
    end
    #= return filter(t->pct_size(t)==min_size, nodes(g)) =#
    return smallest
end

function simplify(n::Map; settings=Dict{Symbol, Bool}())
    map(t->make_node(Map, ff(n), t), simplify(fc(n); settings=settings))
end

function simplify(n::Add; settings=Dict{Symbol, Bool}())
    simplify(add([simplify(t; settings=settings) for t in content(fc(n))]...))
end


function graphs_jl(g::PCTGraph)
    SimpleDiGraph(Edge.(edges(g)))
end

function visualize(g::PCTGraph)
    h = graphs_jl(g)
    label(n::APN) = "$(pretty(n))\n$(pct_size(n))"
    gplothtml(h, nodesize=fill(80, length(nodes(g))), nodelabel=label.(nodes(g)))
end


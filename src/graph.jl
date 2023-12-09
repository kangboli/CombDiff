using GraphPlot, DataStructures

export PCTGraph, nodes, edges, spanning_tree!, graphs_jl, visualize, simplify, propagate_k, custom_settings, symmetry_settings, redux

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

const Settings = Dict{Symbol, Bool}
default_settings = Settings(:clench_sum=>false, :symmetry=>false)
function custom_settings(custom::Vararg{Pair{Symbol, Bool}})::Settings
    new_settings = deepcopy(default_settings)
    for (s, b) in custom
        new_settings[s] = b
    end
    return new_settings
end
const symmetry_settings = custom_settings(:clench_sum=>false, :symmetry=>true)

"""

If there is a sink cluster: return the sink cluster with a `true`.
If there is no sink cluster: traverse the subgraph and 
    1. add the subgraph to seen.
    2. return the subgraph.

"""
function spanning_tree!(n::APN, seen=PCTGraph(); settings=Dict{Symbol, Bool}())
    push!(nodes(seen), n)
    push!(hashset(seen), n)
    node_start, edge_start = (length(nodes(seen)), length(edges(seen)))
    neighbor_list = neighbors(n; settings=settings)
    reduced_list = Vector{Tuple{APN, Bool, String}}()
    @time for (t, d, name) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        t in hashset(seen) || push!(reduced_list, (t, d, name))
    end

    for (t, d, name) in sort(reduced_list, by=e->-e[2])
        push!(edges(seen), node_start=>1+length(nodes(seen)))
        !d && push!(edges(seen), 1+length(nodes(seen))=>node_start)
        log_edge(n, t, d, name, length(nodes(seen)))
        sink, tree = spanning_tree!(t, seen; settings=settings)
        (d || sink) && return (true, tree)
    end

    new_nodes = nodes(seen)[node_start:end]
    new_edges = edge_start == length(edges(seen)) ? Vector{Pair{Int, Int}}() : edges(seen)[edge_start+1:end]
    return false, PCTGraph(new_nodes, new_edges, hashset(seen))
end

function log_edge(n, t, d, name, i)
    println(i, " ", name)
    println(pretty(n))
    println(pretty(t))
    d || println("<->")
    d && println("-->")
    println()
end


function simplify(n::APN; settings=default_settings)
    g = last(spanning_tree!(n; settings=settings))
    min_size = minimum(pct_size, nodes(g))
    smallest = Vector{APN}()

    for n in nodes(g)
        pct_size(n) == min_size && push!(smallest, n)
    end
    return smallest
end

function simplify(n::Map; settings=default_settings)
    map(t->make_node(Map, ff(n), t), simplify(fc(n); settings=settings))
end


function redux(n::Map; settings=default_settings)
    pct_map(ff(n)...,  redux(fc(n); settings=settings))
end

function redux(n::APN; settings=default_settings)
    reduced = [redux(t, settings=settings) for t in content(n)]
    simplify(set_content(n, reduced...); settings=settings) |> first
end

function redux(n::Union{Var, Constant}; _...)
    return n
end

function propagate_k(n::Map, k=constant(1))
    return ecall(n, ff(n)[1:end-1]..., k)
end

function graphs_jl(g::PCTGraph)
    SimpleDiGraph(Edge.(edges(g)))
end

function visualize(g::PCTGraph)
    h = graphs_jl(g)
    label(n::APN) = "$(pretty(n))\n$(pct_size(n))"
    gplothtml(h, nodesize=fill(80, length(nodes(g))), nodelabel=label.(nodes(g)))
end


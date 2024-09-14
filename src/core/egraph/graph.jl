using DataStructures

export PCTGraph, nodes, edges, spanning_tree!, simplify, propagate_k, custom_settings, symmetry_settings, redux, vdiff, Logger, html_report, log_step!, log_time!, mathjax

struct PCTGraph
    nodes::Vector{APN}
    edges::Vector{Pair{Int,Int}}
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

PCTGraph() = PCTGraph(Vector{APN}(), Vector{Pair{Int,Int}}(), RBTree{APN}())


function PCTGraph(n::APN)
    g = PCTGraph(Vector{APN}(), Vector{Pair{Int,Int}}(), RBTree{APN}())
    push!(nodes(g), n)
    push!(hashset(g), n)
    return g
end

const Settings = Dict{Symbol,Bool}
default_settings = Settings(
    :clench_sum => false,
    :symmetry => false,
    :logging => true,
    :gcd => true,
    :blaserize => false,
    :wick => false,
    :dist_conj => false,
    :expand_mul => false,
    :expand_comp => false,
    :dist_ind => true,
    :telescopic_indicator => false,
    :reduce_vac_early => true)
function custom_settings(custom::Vararg{Pair{Symbol,Bool}}; preset=default_settings)::Settings
    new_settings = deepcopy(preset)
    for (s, b) in custom
        new_settings[s] = b
    end
    new_settings[:gcd] && new_settings[:expand_mul] && error(":expand_mul and :gcd cannot be both set.")
    return new_settings
end
const symmetry_settings = custom_settings(:symmetry => true; preset=default_settings)
const blaserize_settings = custom_settings(:blaserize => true; preset=default_settings)

struct Logger
    timers::Vector{Float64}
    steps::Vector{APN}
    names::Vector{String}
end

Logger() = Logger(zeros(Float64, 10), Vector{APN}(), Vector{String}())

function log_time!(l::Logger, i::Int, t::Float64)
    l.timers[i] += t
end

function log_step!(l::Logger, n::APN, name::String)
    push!(l.steps, n)
    push!(l.names, name)
end

function html_report(l::Logger, report_name="tmp")

    timing = "
        <p> Neighbor Listing: $(l.timers[1]) </p>
        <p> Hashing for Seen: $(l.timers[2]) </p>
        "
    paragraphs = join(map((i, t, n) -> "<p> $(i) <code>$(n)</code>: \$\$ $(t) \$\$</p>", 1:length(l.steps), map(latex, l.steps), l.names), "")
    html = """
    <!DOCTYPE html>
    <html lang="en">
    <head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title></title>
    <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<style type="text/css" media="screen">
        body {
        background-color: #11211c;
        color: #b1ecde;
        text-align: center;
        }
</style>
    </head>
    <body>
        <h2>Timing</h2>
    $(timing)
        <h2>History</h2>
    $(paragraphs)
    </body>
    </html>
    """
    f = open("$(report_name).html", "w")
    write(f, html)
    close(f)
    run(`open $(report_name).html`)
end

function mathjax(n::APN)
    l = Logger()
    log_step!(l, n, "MATHJAX")
    html_report(l)
end

"""

If there is a sink cluster: return the sink cluster with a `true`.
If there is no sink cluster: traverse the subgraph and 
    1. add the subgraph to seen.
    2. return the subgraph.

"""
function spanning_tree!(n::APN, seen=PCTGraph(); settings=default_settings, logger=Logger())
    push!(nodes(seen), n)
    node_start, edge_start = (length(nodes(seen)), length(edges(seen)))

    if settings[:blaserize]
        neighbor_list = blaserize_neighbors(n)
    else
        t = @elapsed neighbor_list = neighbors(n; settings=settings)
        log_time!(logger, 1, t)
    end
    reduced_list = Vector{Tuple{APN,Bool,String}}()
    if any(directed(neighbor_list))
        i = findfirst(directed(neighbor_list))
        push!(reduced_list, (nodes(neighbor_list)[i], true, names(neighbor_list)[i]))
    else
        log_time!(logger, 2, @elapsed push!(hashset(seen), n))

        checking_time = @elapsed for (t, d, name) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            t in hashset(seen) || push!(reduced_list, (t, d, name))
        end
        log_time!(logger, 3, checking_time)
    end


    for (t, d, name) in sort(reduced_list, by=e -> -e[2])
        push!(edges(seen), node_start => 1 + length(nodes(seen)))
        !d && push!(edges(seen), 1 + length(nodes(seen)) => node_start)
        #= log_edge(n, t, d, name, length(nodes(seen))) =#
        if settings[:logging]
            log_edge(n, t, d, name, length(nodes(seen)))
            log_step!(logger, t, name)
        end
        sink, tree = spanning_tree!(t, seen; settings=settings, logger=logger)
        (d || sink) && return (true, tree)
    end

    new_nodes = nodes(seen)[node_start:end]
    new_edges = edge_start == length(edges(seen)) ? Vector{Pair{Int,Int}}() : edges(seen)[edge_start+1:end]
    return false, PCTGraph(new_nodes, new_edges, hashset(seen))
end

function log_edge(n, t, d, name, i)
    println(i, " ", name)
    #= println(pretty(n))
    println(typeof(t))
    println(pretty(t)) =#
    d || println("<->")
    d && println("-->")
    println()
end

# function graphs_jl(g::PCTGraph)
#     SimpleDiGraph(Edge.(edges(g)))
# end

# function visualize(g::PCTGraph)
#     h = graphs_jl(g)
#     label(n::APN) = "$(pretty(n))\n$(pct_size(n))"
#     gplothtml(h, nodesize=fill(80, length(nodes(g))), nodelabel=label.(nodes(g)))
# end


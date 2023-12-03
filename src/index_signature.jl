export SignatureTree, subtrees, tree_dfs_vis, node_type

struct SignatureTree <: APN
    type::AbstractPCTType
    node_type::Type  # I avoided parametric type of this intentionally.
    extra::Union{APN, Nothing}
    subtrees::Vector{Pair{SignatureTree,Int}}
end

get_type(sig::SignatureTree) = sig.type
node_type(sig::SignatureTree) = sig.node_type
extra(sig::SignatureTree) = sig.extra
subtrees(sig::SignatureTree) = sig.subtrees

# function tree_bfs(sig::SignatureTree, nodes=Dict{Int,Vector{Pair{Type,Int}}}(0 => [node_type(sig) => 1]), level=0)
#     for (t, i) in subtrees(sig)
#         nodes[level+1] = push!(get(nodes, level + 1, Vector{Pair{Type,Int}}()), node_type(t) => i)
#     end

#     for (t, _) in subtrees(sig)
#         tree_bfs(t, nodes, level + 1)
#     end
#     return nodes
# end

function tree_dfs_vis(sig::SignatureTree, nodes=Vector{Any}([(node_type(sig), extra(sig)) => 1]))
    edges = Vector{Pair{Int,Int}}()
    node_start = length(nodes)
    for (t, i) in subtrees(sig)
        push!(nodes, (node_type(t), extra(t)) => i)
        push!(edges, node_start => length(nodes))
        _, new_edges = tree_dfs_vis(t, nodes)
        append!(edges, new_edges)
    end

    #= for (t, _) in subtrees(sig)
    end =#

    return nodes, edges
end

function Base.show(io::IO, ::MIME"text/plain", sig::SignatureTree)
    print(io, to_string(sig))
end

function to_string(sig::SignatureTree, indent=0, i=nothing)
    str = "$(join(fill(" ", indent)))$(i===nothing ? "" : i): $(node_type(sig)) $(extra(sig) === nothing ? "" : pretty(extra(sig)))\n"
    for (t, i) in subtrees(sig)
        str *= to_string(t, indent+4, i)
    end
    return str
end


function process_content!(sig::SignatureTree, index::S, c::Vector{T}, other_indices::Vector{R}) where {S <: Var, T <:APN, R <: Var}
    for (i, t) in enumerate(c)
        t in other_indices && continue
        subsig = SignatureTree(index, t, other_indices)
        push!(subtrees(sig), subsig => i)
    end
end

function SignatureTree(index::S, summand::T, other_indices::Vector{R}) where {S<:Var,T<:APN,R<:Var}
    sig = SignatureTree(get_type(index), T, nothing, Vector{SignatureTree}())
    process_content!(sig, index, content(summand), other_indices)
    return sig
end

function SignatureTree(index::S, call::T, other_indices::Vector{R}) where {S <: Var, T <: AbstractCall, R <: Var}
    sig = SignatureTree(get_type(index), T, nothing, Vector{SignatureTree}())
    process_content!(sig, index, [mapp(call), content(args(call))...], other_indices)
    return sig
end

function SignatureTree(index::S, summand::T, ::Vector{R}) where {S <: Var, T <: Var, R <: Var}
    
    return SignatureTree(get_type(index), T, index == summand ? nothing : summand, Vector{SignatureTree}())
end

const Commtative = Union{Mul, Add}

function Base.:(==)(sig_1::SignatureTree, sig_2::SignatureTree)
    #= get_type(sig_1) == get_type(sig_2) || println(get_type(sig_1), " vs ",get_type(sig_2)) =#
    get_type(sig_1) == get_type(sig_2) || return false
    #= node_type(sig_1) == node_type(sig_2) || println(node_type(sig_1), " vs ",node_type(sig_2)) =#
    node_type(sig_1) == node_type(sig_2) || return false

    #= if node_type(sig_1) == PrimitiveCall
        first(subtrees(sig_1)) == first(subtrees(sig_2)) || return false
        subtrees(first(last(subtrees(sig_1)))) == 
        subtrees(first(last(subtrees(sig_2)))) || return false
    end =#
    trees_to_compare_1 = subtrees(sig_1)
    trees_to_compare_2 = subtrees(sig_2)
    if node_type(sig_1) <: Commtative
        trees_to_compare_1 = content(first(first.(trees_to_compare_1)))
        trees_to_compare_2 = content(first(first.(trees_to_compare_2)))
    end

    for t in trees_to_compare_1
        n_1 = count(n -> n == t, trees_to_compare_1)
        n_2 = count(n -> n == t, trees_to_compare_2)
        n_1 == n_2 || return false
    end

    #= for (t_1, t_2) in zip(trees_to_compare_1, trees_to_compare_2)
        t_1 == t_2 || println(t_1, " vs ", t_2)
        t_1 == t_2 || return false
    end =#

    return true
end


function Base.hash(p::Pair{SignatureTree, Int})
    return hash(first(p)) + hash(last(p))
end

function Base.hash(sig::SignatureTree)
    own_hash = sum(hash, (get_type(sig), node_type(sig), hash(extra(sig))))
    trees_to_hash = sort(subtrees(sig), by=last)
    if node_type(sig)  <: Commtative
        trees_to_hash = content(first(first.(trees_to_hash)))
    end
    return own_hash * sum(sort(hash.(trees_to_hash)), init=0)
end



export SignatureTree, subtrees, tree_dfs_vis, node_type

struct SignatureTree <: AbstractSignatureTree
    node_type::Type  # I avoided parametric type of this intentionally.
    extra::Union{Var,Constant,Nothing}
    subtrees::Vector{Pair{SignatureTree,Int}}
end

node_type(sig::SignatureTree) = sig.node_type
extra(sig::SignatureTree) = sig.extra
subtrees(sig::SignatureTree) = sig.subtrees

function tree_dfs_vis(sig::SignatureTree, nodes=Vector{Any}([(node_type(sig), extra(sig)) => 1]))
    edges = Vector{Pair{Int,Int}}()
    node_start = length(nodes)
    for (t, i) in subtrees(sig)
        push!(nodes, (node_type(t), extra(t)) => i)
        push!(edges, node_start => length(nodes))
        _, new_edges = tree_dfs_vis(t, nodes)
        append!(edges, new_edges)
    end

    return nodes, edges
end

function Base.show(io::IO, ::MIME"text/plain", sig::SignatureTree)
    print(io, to_string(sig))
end

function to_string(sig::SignatureTree, indent=0, i=nothing)
    str = "$(join(fill(" ", indent)))$(i===nothing ? "" : i): $(node_type(sig)) $(extra(sig) === nothing ? "" : pretty(extra(sig)))\n"
    for (t, i) in subtrees(sig)
        str *= to_string(t, indent + 4, i)
    end
    return str
end


function process_content!(sig::SignatureTree, index::S, c::Vector{T}, other_indices::Vector{R}) where {S<:Var,T<:APN,R<:Var}
    for (i, t) in enumerate(c)
        if isa(t, Var)
            name(t) in name.(other_indices) && continue
        end
        # (isa(t, Var) || contains_name(t, name(index))) || continue
        subsig = SignatureTree(index, t, other_indices)
        push!(subtrees(sig), subsig => i)
    end
end

function SignatureTree(index::S, summand::T, other_indices::Vector{R}) where {S<:Var,T<:APN,R<:Var}
    sig = SignatureTree(T, nothing, Vector{SignatureTree}())
    process_content!(sig, index, content(summand), other_indices)
    return sig
end

function SignatureTree(index::S, call::T, other_indices::Vector{R}) where {S<:Var,T<:AbstractCall,R<:Var}
    sig = SignatureTree(T, nothing, Vector{SignatureTree}())
    process_content!(sig, index, [mapp(call), content(args(call))...], other_indices)
    return sig
end

function SignatureTree(index::S, v::T, ::Vector{R}) where {S<:Var,T<:Var,R<:Var}
    return SignatureTree(T, index == v ? nothing : v, Vector{SignatureTree}())
end

function SignatureTree(::S, c::Constant, ::Vector{R}) where {S<:Var,R<:Var}
    return SignatureTree(Constant, c, Vector{SignatureTree}())
end

const Commtative = Union{Mul,Add}

function Base.:(==)(sig_1::SignatureTree, sig_2::SignatureTree)
    node_type(sig_1) == node_type(sig_2) || return false

    trees_to_compare_1 = subtrees(sig_1)
    trees_to_compare_2 = subtrees(sig_2)
    length(trees_to_compare_1) == length(trees_to_compare_2) || return false
    node_type(sig_1) <: Commtative || return trees_to_compare_1 == trees_to_compare_2

    trees_to_compare_1 = first.(subtrees(first(first(trees_to_compare_1))))
    trees_to_compare_2 = first.(subtrees(first(first(trees_to_compare_2))))
    # trees_to_compare_1 == trees_to_compare_2

    # TODO: Change this to a sort based comparison
    for t in trees_to_compare_1
        n_1 = count(x -> x == t, trees_to_compare_1)
        n_2 = count(x -> x == t, trees_to_compare_2)
        n_1 == n_2 || return false
    end

    return true

end

function trunc_hash(p::Pair{SignatureTree,Int}, level=3)
    return trunc_hash(first(p), level) + hash(last(p))
end

Base.hash(sig::SignatureTree) = trunc_hash(sig)

function trunc_hash(sig::SignatureTree, level=3)
    own_hash = sum(hash, (node_type(sig), hash(extra(sig))))
    level == 0 && return own_hash
    trees_to_hash = subtrees(sig)
    if node_type(sig) <: Commtative
        trees_to_hash = first.(subtrees(first(first(trees_to_hash))))
    end
    hashes = [trunc_hash(t, level - 1) for t in trees_to_hash]
    return own_hash + sum(sort(hashes), init=0)
end



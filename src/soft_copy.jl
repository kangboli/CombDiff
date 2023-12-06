function soft_copy(n::T, symbols::Vector{Symbol}) where T <: APN
    any(s->contains_name(n, s), symbols) || return n
    return make_node(T, [soft_copy(t, symbols) for t  in terms(n)]...; type=get_type(n))
end

function soft_copy(n::Union{Number, Symbol}, ::Vector{Symbol})
    return n
end
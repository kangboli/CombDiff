function Base.:(==)(n_1::R, n_2::S) where {R<:APN,S<:APN}
    R == S || return false
    objectid(n_1) == objectid(n_2) && return true
    t_1, t_2 = terms(n_1), terms(n_2)
    length(t_1) == length(t_2) || return false

    for i = 1:length(t_1)
        t_1[i] == t_2[i] || return false
    end
    return true
end

function Base.hash(n::T, h::UInt) where {T<:APN}
    trunc_hash(n, h, 3)
end

function trunc_hash(n::T, h::UInt, level=3) where {T<:APN}
    result = hash(T, h)
    level == 0 && return result
    return result + reduce(xor, [trunc_hash(t, h, level - 1) for t in terms(n)])
end

Base.:(==)(t_1::T, t_2::T) where {T<:ElementType} = true
trunc_hash(::T, h::UInt, ::Int) where {T<:ElementType} = T.hash
trunc_hash(n::Constant, h::UInt, ::Int) = hash(get_body(n), h)

function Base.hash(v::VecType, h::UInt)
    return reduce(xor, map(t -> hash(t, h), content(v)))
end

function Base.hash(m::MapType, h::UInt)
    return reduce(xor, map(t -> hash(t, h), get_bound_type(m))) + hash(content(m), h)
end


function Base.:(==)(d_1::Domain, d_2::Domain)
    d_1.base == d_2.base &&
        d_1.lower == d_2.lower &&
        d_1.upper == d_2.upper
end

function Base.hash(d::Domain, h::UInt)
    hash(d.base, h) + hash(d.lower, h) + hash(d.upper, h)
end

function Base.:(==)(n_1::Var{R}, n_2::Var{S}) where {R<:AbstractPCTType,S<:AbstractPCTType}
    R == S || return false
    name(n_1) == name(n_2)
end

function trunc_hash(v::Var{T}, h::UInt, ::Int) where {T<:AbstractPCTType}
    return hash(name(v), h) + T.hash
end

remake_node(n::T) where {T<:APN} = make_node(T, terms(n)...; type=get_type(n))

function Base.:(==)(n_1::T, n_2::T) where {T<:Union{Contraction,Prod}}
    objectid(n_1) == objectid(n_2) && return true
    length(get_bound(n_1)) == length(get_bound(n_2)) || return false
    sig_set_1, sig_set_2 = Set(signatures!(n_1)), Set(signatures!(n_2))
    length(sig_set_1) == length(get_bound(n_1)) || return false
    sig_set_1 == sig_set_2 || return false

    symbols = new_symbol(get_body(n_1), get_body(n_2), num=length(signatures!(n_1)))
    variable_map = Dict(sig => s for (sig, s) in zip(signatures!(n_1), symbols))

    # The deepcopy is the performance bottleneck of this package.
    replaced_expr_1 = deepcopy(get_body(n_1))
    for (index, sig) in zip(content(get_bound(n_1)), signatures!(n_1))
        replaced_expr_1 = fast_rename!(replaced_expr_1, index, variable_map[sig])
    end
    replaced_expr_1 = remake_node(replaced_expr_1)

    replaced_expr_2 = deepcopy(get_body(n_2))
    for (index, sig) in zip(content(get_bound(n_2)), signatures!(n_2))
        #= i, sh = Base.hashindex(sig, length(variable_map.keys))
        println(i)
        k = variable_map.keys[i]
        println(Base.isequal(k, sig)) =#
        ks = keys(variable_map)
        sig in ks || return false
        replaced_expr_2 = fast_rename!(replaced_expr_2, index, variable_map[sig])
    end
    replaced_expr_2 = remake_node(replaced_expr_2)

    return replaced_expr_1 == replaced_expr_2
end

function trunc_hash(n::T, h::UInt, level=3) where {T<:Contraction}
    level == 0 && return hash(T, h)

    dummy_removed = deepcopy(get_body(n))
    for index in content(get_bound(n))
        dummy_removed = fast_rename!(dummy_removed, index, :dummy)
    end
    symbols = new_symbol(dummy_removed, num=length(signatures!(n)))
    variable_map = Dict(sig => s for (sig, s) in zip(signatures!(n), symbols))

    replaced_expr = deepcopy(get_body(n))
    for (index, sig) in zip(content(get_bound(n)), signatures!(n))
        replaced_expr = fast_rename!(replaced_expr, index, variable_map[sig])
    end
    return reduce(xor, map(t -> hash(t, h), signatures!(n))) + trunc_hash(replaced_expr, h, level - 1)
end

function Base.:(==)(n_1::T, n_2::T) where {T<:Union{Mul,Add}}
    objectid(n_1) == objectid(n_2) && return true
    c_1, c_2 = content(get_body(n_1)), content(get_body(n_2))
    length(c_1) == length(c_2) || return false
    return c_1 == c_2
end

function Base.hash(n::T, h::UInt) where {T<:Union{Mul,Add}}
    hashes = map(t -> hash(t, h), content(get_body(n)))
    return reduce(xor, hashes) + hash(T, h) + h
end

function Base.:(==)(v_1::VecType, v_2::VecType)
    objectid(v_1) == objectid(v_2) && return true
    length(v_1) == length(v_2) &&
        all(i -> get_content_type(v_1)[i] == get_content_type(v_2)[i], 1:length(v_1))
end


function Base.:(==)(m_1::MapType, m_2::MapType)
    objectid(m_1) == objectid(m_2) && return true
    get_bound_type(m_1) == get_bound_type(m_2) && get_body_type(m_1) == get_body_type(m_2)
end

function Base.:(==)(d_1::T, d_2::T) where {T<:AbstractDelta}

    if upper(d_1) == upper(d_2)
        lower(d_1) == lower(d_2) || return false
    elseif upper(d_1) == lower(d_2)
        lower(d_1) == upper(d_2) || return false
    else
        return false
    end

    get_body(d_1) == get_body(d_2)
end


function pct_size(n::APN)
    return sum(pct_size, content(n)) + 1
end

pct_size(v::TerminalNode) = 1

function Base.isless(n_1::R, n_2::S) where {R<:APN,S<:APN}
    R == S || return R.hash < S.hash
    objectid(n_1) == objectid(n_2) && return false

    t_1, t_2 = terms(n_1), terms(n_2)
    length(t_1) == length(t_2) || return length(t_1) < length(t_2)

    for i = 1:length(t_1)
        t_1[i] == t_2[i] || return t_1[i] < t_2[i]
    end

    return false
end

function Base.isless(v_1::Var{R}, v_2::Var{S}) where {R<:AbstractPCTType,S<:AbstractPCTType}
    R == S || return R.hash < S.hash
    return hash(name(v_1)) < hash(name(v_2))
end


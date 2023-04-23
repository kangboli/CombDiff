function Base.:(==)(n_1::R, n_2::S) where {R <: APN, S <: APN}
    R == S || return false
    objectid(n_1) == objectid(n_2) && return true
    t_1, t_2 = terms(n_1), terms(n_2)
    length(t_1) == length(t_2) || return false

    for i = 1:length(t_1)
        t_1[i] == t_2[i] || return false
    end
    return true
end

function Base.hash(n::APN)
    prod(hash, terms(n))
end

Base.:(==)(t_1::T, t_2::T) where T <: ElementType = true
Base.hash(::T) where T <: ElementType = T.hash
    

function Base.:(==)(d_1::Domain, d_2::Domain)
    d_1.base == d_2.base &&
    d_1.lower == d_2.lower &&
    d_1.upper == d_2.upper 
end

function Base.hash(d::Domain)
    hash(d.base) + hash(d.lower) + hash(d.upper)
end

function Base.:(==)(n_1::Var{R}, n_2::Var{S}) where {R <: AbstractPCTType, S <: AbstractPCTType}
    #= R == S || return false =#
    name(n_1) == name(n_2) # && get_type(n_1) == get_type(n_2)
end

function Base.hash(v::Var{T}) where T <: AbstractPCTType
    return hash(name(v)) + T.hash
    # hash(get_type(v))
end

function Base.:(==)(n_1::T, n_2::T) where T <: Union{Contraction, Prod}
    objectid(n_1) == objectid(n_2) && return true

    #= f_1, f_2 = ff(n_1), ff(n_1) =#
    #= get_type(f_1) == get_type(f_2) || return false =#
    #= ff(n_1) == ff(n_2) && fc(n_1) == fc(n_2) && return true =#
    ff(n_1) == ff(n_2) && fc(n_1) == fc(n_2)
    #= f_1 == f_2 && return fc(n_1) == fc(n_2) =#
    #= return false =#
    #= num_1 = length(f_1) =#

    #= ds = Vector{Var}(undef, num_1)
    d_symbols = new_symbol(n_1, n_2, num=num_1)
    for (i, s, t) in zip(1:num_1, d_symbols, get_type.(f_1))
        ds[i] = make_node(Var, s; type=t)
    end

    s_1 = fc(n_1)
    for (o, d) in zip(f_1, ds)
        s_1 = subst(s_1, o, d)
    end

    s_2 = fc(n_2)
    for (o, d) in zip(f_1, ds)
        s_2 = subst(s_2, o, d)
    end =#

    #= return s_1 == s_2 =#
    #= d = make_node(Var, Symbol(rand()); type=get_type(ff(n_1))) =#
end

function Base.hash(n::T) where T <: Contraction
    #= l = length(content(ff(n)))

    ds = Vector{Var}(undef, l)
    for (i, t) in zip(1:l, get_type.(content(ff(n))))
        ds[i] = make_node(Var, Symbol(string("_tmp_", i)); type=t)
    end

    tmp = fc(n)
    for (o, d) in zip(content(ff(n)), ds)
        tmp = subst(tmp, o, d)
    end

    es = Vector{Var}(undef, l)
    for (i, s, t) in zip(1:l, new_symbol(tmp, num=length(ff(n))), get_type.(content(ff(n))))
        es[i] = make_node(Var, s; type=t)
    end

    for (o, d) in zip(content(ff(n)), es)
        tmp = subst(tmp, o, d)
    end =#


    return hash(ff(n)) + hash(fc(n)) + T.hash
end

function Base.:(==)(n_1::T, n_2::T) where T <: Union{Mul, Add}
    objectid(n_1) == objectid(n_2) && return true
    c_1, c_2 = content(fc(n_1)), content(fc(n_2))
    length(c_1) == length(c_2) || return false
    for t in c_1
        t in c_2 || return false
    end
    return true
end

function Base.hash(n::T) where T <: Union{Mul, Add}
    sorted_v = sort(content(fc(n)), by=hash)
    return prod(hash, sorted_v) + T.hash
end

function Base.:(==)(v_1::VecType, v_2::VecType)
    length(v_1) == length(v_2) &&
    all(i->content(v_1)[i] == content(v_2)[i], 1:length(v_1))
end

function Base.:(==)(m_1::MapType, m_2::MapType)
    from(m_1) == from(m_2) && content(m_1) == content(m_2)
end

function Base.:(==)(d_1::T, d_2::T) where T <: AbstractDelta

    if upper(d_1) == upper(d_2)
        lower(d_1) == lower(d_2) || return false
    elseif upper(d_1) == lower(d_2)
        lower(d_1) == upper(d_2) || return false
    else
        return false
    end

    fc(d_1) == fc(d_2)
end


function pct_size(n::APN)
    return sum(pct_size, content(n)) + 1
end

pct_size(v::TerminalNode) = 1
    
function Base.isless(n_1::R, n_2::S) where {R <: APN, S <: APN}
    R == S || return R.hash < S.hash
    objectid(n_1) == objectid(n_2) && return false

    t_1, t_2 = terms(n_1), terms(n_2)
    length(t_1) == length(t_2) || return length(t_1) < length(t_2) 

    for i = 1:length(t_1)
        t_1[i] == t_2[i] || return t_1[i] < t_2[i]
    end

    return false
end

function Base.isless(v_1::Var{R}, v_2::Var{S}) where {R <: AbstractPCTType, S <: AbstractPCTType}
    R == S || return R.hash < S.hash
    return hash(name(v_1)) < hash(name(v_2))
end


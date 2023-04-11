function Base.:(==)(n_1::T, n_2::T) where T <: APN
    t_1, t_2 = terms(n_1), terms(n_2)
    return length(t_1) == length(t_2) && 
    all(i->t_1[i] == t_2[i], 1:length(terms(n_1)))
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
    hash(d.base) * hash(d.lower) * hash(d.upper)
end

function Base.:(==)(n_1::Var, n_2::Var)
    name(n_1) == name(n_2) && 
    get_type(n_1) == get_type(n_2)
end

function Base.hash(v::Var)
    return hash(name(v)) * hash(get_type(v))
end

function Base.:(==)(n_1::T, n_2::T) where T <: Union{Contraction, Prod}
    get_type(ff(n_1)) == get_type(ff(n_2)) || return false

    #= ff(n_1) == ff(n_2) && fc(n_1) == fc(n_2) && return true =#
    d = make_node(Var, first(new_symbol(n_1, n_2)); type=get_type(ff(n_1)))
    #= d = make_node(Var, Symbol(rand()); type=get_type(ff(n_1))) =#
    return subst(fc(n_1), ff(n_1), d) == subst(fc(n_2), ff(n_2), d)
end

function Base.hash(n::T) where T <: Contraction
    d = make_node(Var, first(new_hash(n)); type=get_type(ff(n)))
    return hash(subst(fc(n), ff(n), d)) * T.hash
end

function Base.:(==)(n_1::T, n_2::T) where T <: Union{Mul, Add}
    Set(content(fc(n_1))) == Set(content(fc(n_2)))
end

function Base.hash(n::T) where T <: Union{Mul, Add}
    sorted_v = sort(content(fc(n)), by=hash)
    return prod(hash, sorted_v) * T.hash
end


function Base.:(==)(v_1::VecType, v_2::VecType)
    length(v_1) == length(v_2) &&
    all(i->content(v_1)[i] == content(v_2)[i], 1:length(v_1))
end

function Base.:(==)(m_1::MapType, m_2::MapType)
    from(m_1) == from(m_2) && content(m_1) == content(m_2)
end

function Base.:(==)(d_1::T, d_2::T) where T <: AbstractDelta
    Set([upper(d_1), lower(d_1)]) == Set([upper(d_2), lower(d_2)]) && fc(d_1) == fc(d_2)
end


function pct_size(n::APN)
    return sum(pct_size, content(n)) + 1
end

pct_size(v::TerminalNode) = 1
    
Base.isless(n_1::APN, n_2::APN) = hash(n_1) < hash(n_2)


function Base.:(==)(n_1::T, n_2::T) where T <: APN
    t_1, t_2 = terms(n_1), terms(n_2)
    return length(t_1) == length(t_2) && 
    all(i->t_1[i] == t_2[i], 1:length(terms(n_1)))
end

function Base.hash(n::APN)
    prod(hash, terms(n))
end

function Base.:(==)(n_1::Var, n_2::Var)
    n_1.content == n_2.content
end

function Base.hash(v::Var)
    return hash(v.content)
end

function Base.:(==)(p_1::PrimitiveCall, p_2::PrimitiveCall)
    return p_1.mapp == p_2.mapp && 
    p_1.args == p_2.args
    
end

function Base.hash(p::PrimitiveCall)
    hash(p.mapp) * prod(hash, p.args)
end




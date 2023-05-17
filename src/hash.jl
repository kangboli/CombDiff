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
    name(n_1) == name(n_2) 
end

function Base.hash(v::Var{T}) where T <: AbstractPCTType
    return hash(name(v)) + T.hash
end

function Base.:(==)(n_1::T, n_2::T) where T <: Union{Contraction, Prod}
    objectid(n_1) == objectid(n_2) && return true
    content(ff(n_1)) == content(ff(n_2)) && return fc(n_1) == fc(n_2)
    #= ff_1_new = Vector{APN}()
    for f in free_variables(fc(n_1))
        f in content(ff(n_1)) && push!(ff_1_new, f)
    end

    ff_2_new = Vector{APN}()
    for f in free_variables(fc(n_2))
        f in content(ff(n_2)) && push!(ff_2_new, f)
    end =#

    ff_1, fc_1 = renaming(content(ff(n_1)), fc(n_1))
    ff_2, fc_2 = renaming(content(ff(n_2)), fc(n_2))

    ff_1 == ff_2 && fc_1 == fc_2 && return true
end

function Base.hash(n::T) where T <: Contraction
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

function renaming(original::Vector, n::APN)
    l = length(original)

    tmp_vars = Vector{Var}()
    for (s, t) in zip(new_symbol(n; num=l, namespace=:_tmp_), get_type.(original))
        push!(tmp_vars, make_node(Var, s; type=t))
    end

    tmp = n
    for (o, d) in zip(original, tmp_vars)
        tmp = subst(tmp, o, d)
    end

    std_vars = Vector{Var}()
    for (s, t) in zip(new_symbol(tmp, num=l), get_type.(tmp_vars))
        push!(std_vars, make_node(Var, s; type=t))
    end

    for (o, d) in zip(tmp_vars, std_vars)
        tmp = subst(tmp, o, d)
    end

    return std_vars, tmp
end

function renaming(original::Vector, new::Vector{Var}, n::APN)
    l = length(original)

    tmp_vars = Vector{Var}()
    for (s, t) in zip(new_symbol(n; num=l, namespace=:_tmp_), get_type.(original))
        push!(tmp_vars, make_node(Var, s; type=t))
    end

    tmp = n
    for (o, d) in zip(original, tmp_vars)
        tmp = subst(tmp, o, d)
    end

    n = tmp
    for (o, d) in zip(tmp_vars, new)
        n = subst(n, o, d)
    end

    return n
end




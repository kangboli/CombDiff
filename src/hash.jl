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

function Base.hash(n::T) where T <: APN
    # sum(PCT.hash, terms(n))
    trunc_hash(n, 3)
end

function trunc_hash(n::T, level=3) where T <: APN
    result = T.hash
    level == 0 && return result
    return result + sum(trunc_hash(t, level-1) for t in terms(n))
end

Base.:(==)(t_1::T, t_2::T) where T <: ElementType = true
# Base.hash(::T) where T <: ElementType = T.hash
trunc_hash(::T, ::Int) where T <: ElementType = T.hash
trunc_hash(n::Constant, ::Int) = hash(fc(n))
    

function Base.:(==)(d_1::Domain, d_2::Domain)
    d_1.base == d_2.base &&
    d_1.lower == d_2.lower &&
    d_1.upper == d_2.upper 
end

function Base.hash(d::Domain)
    hash(d.base) + hash(d.lower) + hash(d.upper)
end

function Base.:(==)(n_1::Var{R}, n_2::Var{S}) where {R <: AbstractPCTType, S <: AbstractPCTType}
    R == S || return false
    name(n_1) == name(n_2) # && get_type(n_1) == get_type(n_2)
end

# function Base.hash(v::Var{T}) where T <: AbstractPCTType
#     return hash(name(v)) + T.hash
#     # hash(get_type(v))
# end
function trunc_hash(v::Var{T}, ::Int) where T <: AbstractPCTType
    return hash(name(v)) + T.hash
end

function Base.:(==)(n_1::T, n_2::T) where T <: Union{Contraction, Prod}
    objectid(n_1) == objectid(n_2) && return true

    #= f_1, f_2 = ff(n_1), ff(n_1) =#
    #= get_type(f_1) == get_type(f_2) || return false =#
    #= ff(n_1) == ff(n_2) && fc(n_1) == fc(n_2) && return true =#
    
    length(ff(n_1)) == length(ff(n_2)) || return false
    # signatures_1 = [SignatureTree(ff(n_1)[i], fc(n_1), content(ff(n_1))[1:end .!= i]) for i in 1:length(ff(n_1))]
    # set_1 = Set(signatures_1)
    # signatures_2 = Vector{SignatureTree}()
    # for i in 1:length(ff(n_2))
    #     sig = SignatureTree(ff(n_2)[i], fc(n_2), content(ff(n_2))[1:end .!= i])
    #     sig in set_1 || return false
    #     push!(signatures_2, sig)
    # end

    #= println(issetequal(Set(signatures_1), Set(signatures_2))) =#
    #= println(to_string(signatures_1[1]))
    println(to_string(signatures_2[1])) =#

    # Set(signatures_1) == Set(signatures_2) || return false
    # println(Set(signatures!(n_1)) == Set(signatures!(n_2)))
    Set(signatures!(n_1)) == Set(signatures!(n_2)) || return false
    symbols = new_symbol(fc(n_1), fc(n_2), num=length(signatures!(n_1)))
    variable_map = Dict(sig => s for (sig, s) in zip(signatures!(n_1), symbols))

    replaced_expr_1 = deepcopy(fc(n_1))
    # replaced_expr_1 = soft_copy(fc(n_1), name.(content(ff(n_1))))
    for (index, sig) in zip(content(ff(n_1)), signatures!(n_1))
        replaced_expr_1 = fast_rename!(replaced_expr_1, index, variable_map[sig])
    end
    replaced_expr_1 = remake_node(replaced_expr_1)


    replaced_expr_2 = deepcopy(fc(n_2))
    # replaced_expr_2 = soft_copy(fc(n_2), name.(content(ff(n_2))))
    for (index, sig) in zip(content(ff(n_2)), signatures!(n_2))
        replaced_expr_2 = fast_rename!(replaced_expr_2, index, variable_map[sig])
    end
    replaced_expr_2 = remake_node(replaced_expr_2)
    # println(pretty(replaced_expr_1))
    # println(pretty(replaced_expr_2))

    return replaced_expr_1 == replaced_expr_2
    

    #= ff(n_1) == ff(n_2) && fc(n_1) == fc(n_2) =#
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

# function Base.hash(n::T) where T <: Contraction
function trunc_hash(n::T, level=3) where T <: Contraction
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


    #= return hash(ff(n)) + hash(fc(n)) + T.hash =#
    level == 0 && return T.hash

    # signatures = [SignatureTree(ff(n)[i], fc(n), content(ff(n))[1:end .!= i]) for i in 1:length(ff(n))]
    #= println.(to_string.(signatures)) =#
    dummy_removed = deepcopy(fc(n))
    for index in content(ff(n))
        # dummy = var(:dummy, get_type(index))
        dummy_removed = fast_rename!(dummy_removed, index, :dummy)
    end
    symbols = new_symbol(dummy_removed, num=length(signatures!(n)))
    variable_map = Dict(sig => s for (sig, s) in zip(signatures!(n), symbols))

    replaced_expr = deepcopy(fc(n))
    for (index, sig) in zip(content(ff(n)), signatures!(n))
        # replaced_expr = subst(replaced_expr, index, variable_map[sig], true)
        replaced_expr = fast_rename!(replaced_expr, index, variable_map[sig])
    end
    return sum(hash.(signatures!(n))) + trunc_hash(replaced_expr, level-1)
end

function Base.:(==)(n_1::T, n_2::T) where T <: Union{Mul, Add}
    objectid(n_1) == objectid(n_2) && return true
    c_1, c_2 = content(fc(n_1)), content(fc(n_2))
    length(c_1) == length(c_2) || return false
    # return sort!(c_1) == sort!(c_2)
    return c_1 == c_2
end

function Base.hash(n::T) where T <: Union{Mul, Add}
    hashes = hash.(content(fc(n)))
    # sorted_v = sort(, by=hash)
    return sum(hashes) + T.hash
end

function Base.:(==)(v_1::VecType, v_2::VecType)
    objectid(v_1) == objectid(v_2) && return true
    length(v_1) == length(v_2) &&
    all(i->content(v_1)[i] == content(v_2)[i], 1:length(v_1))
end

function Base.:(==)(m_1::MapType, m_2::MapType)
    objectid(m_1) == objectid(m_2) && return true
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
        # hash(t_1[i]) == hash(t_2[i]) || return t_1[i] < t_2[i]
        # t_1[i] != t_2[i] 
        t_1[i] == t_2[i] || return t_1[i] < t_2[i]
    end

    return false
end

function Base.isless(v_1::Var{R}, v_2::Var{S}) where {R <: AbstractPCTType, S <: AbstractPCTType}
    R == S || return R.hash < S.hash
    return hash(name(v_1)) < hash(name(v_2))
end


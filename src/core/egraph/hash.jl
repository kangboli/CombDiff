export perms

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

remake_node(n::T) where {T<:APN} = make_node(T, remake_node.(terms(n))...; type=get_type(n))
remake_node(n::Symbol) = n
remake_node(n::Number) = n


perms(v) = isempty(v) ? [[]] : [[t, p...] for (i, t) in enumerate(v) for p in perms(v[1:end.!=i])]

struct VMap
    d::Dict{SignatureTree,Pair{Int,Vector{Symbol}}}
end

function VMap(d::Dict{SignatureTree,Vector{Symbol}})
    VMap(Dict(k => (0 => v) for (k, v) in d))
end

function Base.getindex(vm::VMap, sig::SignatureTree)
    counter, symbols = vm.d[sig]
    #= isempty(symbols) && error("signatures depleted") =#
    counter += 1
    vm.d[sig] = counter => symbols
    return symbols[counter]
end

function reset!(v::VMap)
    for k in keys(v.d)
        v.d[k] = 0 => last(v.d[k])
    end
end

struct VMapGenerator
    symbols::Vector{Symbol}
    sigs::Vector{SignatureTree}
end

function all_maps(vmg::VMapGenerator)
    d = Dict{SignatureTree,Vector{Symbol}}()
    for (s, sig) in zip(vmg.symbols, vmg.sigs)
        d[sig] = push!(get(d, sig, []), s)
    end

    unique_sigs = filter(((_, v),) -> length(v) == 1, d)
    dup_sigs = filter(((_, v),) -> length(v) >= 1, d)

    return [VMap(merge(unique_sigs, g)) for g in perm_maps(dup_sigs)]
end

function perm_maps(d_dup::Dict{SignatureTree,Vector{Symbol}})
    length(d_dup) == 0 && return [d_dup]

    k, rest... = keys(d_dup)
    result = []
    for v in perms(d_dup[k])
        for g in perm_maps(Dict(r => d_dup[r] for r in rest))
            push!(result, merge(Dict(k => v), g))
        end
    end
    return result
end

#= function gen_maps(d::Dict{SignatureTree, Vector{Symbol}})
    d_dup = filter((_, v) -> length(v) > 1, d)
    length(d_dup) == 0 && return [d]

    k, rest... = keys(d_dup)


    length(d_dup) == 1 && return [Dict(first(keys(d)) => p) for p in perms(first(values(d)))]

end =#




function Base.:(==)(n_1::T, n_2::T) where {T<:Union{Contraction,Prod}}
    objectid(n_1) == objectid(n_2) && return true
    length(get_bound(n_1)) == length(get_bound(n_2)) || return false
    sig_set_1, sig_set_2 = Set(signatures!(n_1)), Set(signatures!(n_2))
    # This is to make a term equal to itself when there are identical signatures.
    sig_set_1 == sig_set_2 || return false
    #= if length(sig_set_1) !== length(get_bound(n_1))
        literal_match = get_bound(n_1) == get_bound(n_2) && get_body(n_1) == get_body(n_2)
        #= literal_match || @warn "duplicated index signatures $(pretty(n_1)) vs $(pretty(n_2))" =#
        return literal_match
    end =#

    symbols = new_symbol(get_body(n_1), get_body(n_2), num=length(signatures!(n_1)))
    vmg = VMapGenerator(symbols, signatures!(n_1))

    for variable_map in all_maps(vmg)
        #= = Dict(sig => s for (sig, s) in zip(signatures!(n_1), symbols)) =#

        # The deepcopy is the performance bottleneck of this package.
        #= replaced_expr_1 = deepcopy(get_body(n_1)) =#
        replaced_expr_1 = remake_node(get_body(n_1))
        for (index, sig) in zip(content(get_bound(n_1)), signatures!(n_1))
            replaced_expr_1 = fast_rename!(replaced_expr_1, index, variable_map[sig])
        end
        # A remake is necessary because renaming breaks e_class invariants.
        replaced_expr_1 = remake_node(replaced_expr_1)

        reset!(variable_map)
        #= replaced_expr_2 = deepcopy(get_body(n_2)) =#
        replaced_expr_2 = remake_node(get_body(n_2))
        for (index, sig) in zip(content(get_bound(n_2)), signatures!(n_2))
            #= ks = keys(variable_map)
            sig in ks || return false =#
            replaced_expr_2 = fast_rename!(replaced_expr_2, index, variable_map[sig])
        end
        replaced_expr_2 = remake_node(replaced_expr_2)

        replaced_expr_1 == replaced_expr_2 && return true
    end
    return false
end

function trunc_hash(n::T, h::UInt, level=3) where {T<:Contraction}
    level == 0 && return hash(T, h)

    #= dummy_removed = deepcopy(get_body(n)) =#
    dummy_removed = remake_node(get_body(n))
    for index in content(get_bound(n))
        dummy_removed = fast_rename!(dummy_removed, index, :dummy)
    end
    symbols = new_symbol(dummy_removed, num=length(signatures!(n)))
    variable_map = Dict(sig => s for (sig, s) in zip(signatures!(n), symbols))

    #= replaced_expr = deepcopy(get_body(n)) =#
    replaced_expr = remake_node(get_body(n))
    for (index, sig) in zip(content(get_bound(n)), signatures!(n))
        replaced_expr = fast_rename!(replaced_expr, index, variable_map[sig])
    end
    return reduce(xor, map(t -> hash(t, h), signatures!(n))) + trunc_hash(replaced_expr, h, level - 1)
end
function Base.:(==)(n_1::Add, n_2::Add) 
    objectid(n_1) == objectid(n_2) && return true
    c_1, c_2 = content(get_body(n_1)), content(get_body(n_2))
    length(c_1) == length(c_2) || return false
    return sort(c_1) == sort(c_2)
end

function Base.:(==)(n_1::Mul, n_2::Mul) 
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


function pct_size(n::APN, scope=1)
    return sum(t->pct_size(t, scope), content(n)) 
end

pct_size(v::Conjugate, scope=1) = 1 + pct_size(get_body(v), scope)
pct_size(::TerminalNode, scope=1) = scope
# negation must not be counted as increasing the size.
# otherwise some symmetries will be prefered over other symmetries
# and the simplification will not consider all symmetries.
pct_size(c::Constant, _=1) = abs(get_body(c)) == 1 ? 0 : 1
function pct_size(s::Sum, scope=1) 
    result = length(get_bound(s)) + pct_size(get_body(s), scope+length(get_bound(s)))
    return result
end


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

function Base.hash(n::Map, h::UInt)
    new_vars = map(var, new_symbol(get_body(n); num=length(args(n))), get_type.(args(n)))
    return hash(ecall(n, new_vars), h)
end

function Base.:(==)(a::Map, b::Map)
    length(get_bound(a)) == length(get_bound(b)) || return false
    new_vars = map(var, new_symbol(a, b; num=length(get_bound(a))), get_type.(get_bound(a)))
    new_a = ecall(a, new_vars...)
    new_b = ecall(b, new_vars...)
    return new_a == new_b
end

#= function inference_if_needed(::Type{T}, ::UndeterminedPCTType, terms::Vararg) where T <: APN
    return T(partial_inference(T, terms...), terms...)
end

function inference_if_needed(::Type{T}, type::S, terms::Vararg) where {T <: APN, S <: AbstractPCTType}
    return T(type, terms...)
end
 =#

"""
    e_class_reduction(T, terms)

Reduce a term to one of the canonical ones within is e-class.
"""
function e_class_reduction(::Type{T}, terms::Vararg) where {T<:APN}
    return T, collect(terms), partial_inference(T, terms...)
end

function e_class_reduction(::Type{Conjugate}, term::T) where {T<:APN}
    t = get_type(term)
    t in [Z(), I(), R()] && return T, terms(term), get_type(term)
    process_type(::Type{Mul}) = Mul, [pct_vec(map(conjugate, content(fc(term)))...)]
    process_type(::Type{Constant}) = Constant, [fc(term)']
    process_type(::Type{T}) where T <: Contraction = T, [ff(term), conjugate(fc(term))]
    process_type(::Type{Delta}) = Delta, [lower(term), upper(term), conjugate(fc(term))]
    process_type(::Type{Conjugate}) = typeof(fc(term)), terms(fc(term))
    process_type(::Type{<:APN}) = Conjugate, [term]
    function inferenced_type(::Type{T}) where T 
        S, terms = process_type(T)
        partial_inference(S, terms...)
    end
    inferenced_type(::Type{Conjugate}) = get_type(fc(term))
    return process_type(T)..., inferenced_type(T)
end


function e_class_reduction(::Type{PrimitiveCall}, mapp::Var, args::PCTVector)
    get_type(mapp) == UndeterminedPCTType() && return PrimitiveCall, [mapp, args], UndeterminedPCTType()
    return PrimitiveCall, [mapp, args], partial_inference(PrimitiveCall, mapp, args)
end


function e_class_reduction(::Type{Monomial}, base::T, power::APN) where {T<:APN}
    is_zero(base) && return Constant, [0], I()
    is_zero(power) && return Constant, [1], Z()
    is_one(power) && return T, terms(base), get_type(base)
    isa(base, Constant) && isa(power, Constant) && return Constant, [fc(base)^fc(power)], partial_inference(Constant, [fc(base)^fc(power)])
    return Monomial, [base, power], partial_inference(Monomial, base, power)
end

function combine_factors(terms::Vector)
    term_dict = Dict{APN, Number}()
    function process_term!(a::Constant)
        term_dict[constant(1)] = fc(a) + get(term_dict, constant(1), 0)
    end
    function process_term!(a::Mul)
        is_constant = group(t->isa(t, Constant), content(fc(a)))
        constant_term = get(is_constant, true, [constant(1)]) |> first
        rest = mul(get(is_constant, false, [])...)
        term_dict[rest] = fc(constant_term) + get(term_dict, rest, 0)
    end
    function process_term!(a::APN)
        term_dict[a] = 1 + get(term_dict, a, 0)
    end
    
    map(process_term!, terms)
    return [v == 1 ? k : mul(constant(v), k) for (k, v) in term_dict if v != 0]
end

function combine_maps(terms::Vector)
    map_dict, remaining_terms = Dict{Int, Vector{APN}}(), Vector{APN}()
    function process_term!(a::Map)
        map_dict[length(ff(a))] = push!(get(map_dict, length(ff(a)), []), a)
    end

    process_term!(a::APN) = push!(remaining_terms, a)
    map(process_term!, terms)

    function process_kv(v)
        vs = ff(v[1])
        have_common_names = all(i->name.(ff(v[i]))==name.(vs), 1:length(v))
        new_from = have_common_names ? vs : pct_vec(map(var, 
        new_symbol(v...; num=length(vs), symbol=:_a), get_type.(vs))...)
        return pct_map(new_from..., add([ecall(x, new_from...) for x in v]...))
    end

    new_maps = [process_kv(v) for (_, v) in map_dict]
    return [remaining_terms..., new_maps...]
end

flatten_add(a::APN) = [a]
flatten_add(a::Add) = vcat(flatten_add.(content(fc(a)))...)

function e_class_reduction(::Type{Add}, term::PCTVector)
    new_terms = vcat(flatten_add.(content(term))...)
    d = group(t->isa(t, Constant), new_terms)
    const_term = sum(map(fc, get(d, true, [])), init=0) |> constant
    new_terms = filter(t -> !is_zero(t), [const_term,  get(d, false, [])...])
    new_terms = combine_factors(new_terms)

    if count(a->isa(a, Map), new_terms) > 1
        new_terms = combine_maps(new_terms)
    end

    sort!(new_terms)
    length(new_terms) == 0 && return Constant, [0], I()
    length(new_terms) == 1 && return typeof(first(new_terms)), terms(first(new_terms)), get_type(first(new_terms))

    return Add, [pct_vec(new_terms...)], partial_inference(Add, pct_vec(new_terms...)) 
end


function e_class_reduction(::Type{T}, from::PCTVector, summand::S) where {T <: Contraction, S<:APN}

    is_zero(summand) && return Constant, [0], partial_inference(Constant, 0)
    # is_one(summand) && T == Prod && return Constant, [1], partial_inference(Constant, 1)
    isempty(content(from)) && return S, terms(summand), get_type(summand)
    if T == S 
        new_from = pct_vec(content(from)..., content(ff(summand))...)
        return T, [new_from, fc(summand)], partial_inference(Sum, new_from, fc(summand))
    end

    if isa(summand, Map)
        fcsummand, ffsummand = fc(summand), ff(summand)
        new_sum = pct_sum(from..., fcsummand)
        return Map, [ffsummand, new_sum], partial_inference(Map, ffsummand, new_sum)
    end

    T, [from, summand], partial_inference(Sum, from, summand)
end

flatten_mul(a::Mul) = vcat(flatten_mul.(content(fc(a)))...)
flatten_mul(a::APN) = [a]

function e_class_reduction(::Type{Mul}, term::PCTVector)
    args = vcat(flatten_mul.(content(term))...)
    is_constant = group(t -> isa(t, Constant), args)
    args_const = get(is_constant, true, [])
    args = [constant(prod(fc, args_const, init=1.0)), get(is_constant, false, [])...]
    args = filter(t -> !is_one(t), args)
    any(is_zero, args) && return Constant, [0], I()
    isempty(args) && return Constant, [1], Z()
    sort!(args)
    if length(args) == 1
        return typeof(first(args)), terms(first(args)), get_type(first(args))
    end
    return Mul, [pct_vec(args...)], partial_inference(Mul, pct_vec(args...))
end




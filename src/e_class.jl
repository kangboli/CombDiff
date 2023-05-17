
"""
    e_class_reduction(T, terms)

Reduce a term to one of the canonical ones within is e-class.
"""
function e_class_reduction(::Type{T}, terms::Vararg) where {T<:APN}
    return T, collect(terms), partial_inference(T, terms...)
end

function e_class_reduction(::Type{PrimitiveCall}, mapp::T, args::PCTVector) where T <: APN
    if T == Map
        return Call, [mapp, args], partial_inference(Call, mapp, args)
    end
    return PrimitiveCall, [mapp, args], partial_inference(PrimitiveCall, mapp, args)
end


function e_class_reduction(::Type{PrimitiveCall}, mapp::Var, args::PCTVector)
    get_type(mapp) == UndeterminedPCTType() && return PrimitiveCall, [mapp, args], UndeterminedPCTType()
    syms = symmetries(get_type(mapp))

    #= type = partial_inference(PrimitiveCall, mapp, args) =#
    graph = dfs(PrimitiveCall(UndeterminedPCTType(), mapp, args), syms)
    result = first(sort(graph, by=get_call))
    return typeof(result), terms(result), partial_inference(typeof(result), terms(result)...)
end


function e_class_reduction(::Type{Monomial}, base::T, power::APN) where {T<:APN}
    is_zero(base) && return Constant, [0], I()
    is_zero(power) && return Constant, [1], I()
    is_one(power) && return T, terms(base), get_type(base)
    isa(base, Constant) && isa(power, Constant) && return Constant, [fc(base)^fc(power)], partial_inference(Constant, [fc(base)^fc(power)])
    return Monomial, [base, power], partial_inference(Monomial, base, power)
end

function e_class_reduction(::Type{Add}, term::PCTVector)
    args = vcat(flatten_add.(content(term))...)
    args = filter(t -> !is_zero(t), args)
    isempty(args) && return Constant, [0], I()
    sort!(args)
    length(args) == 1 && return typeof(first(args)), terms(first(args)), get_type(first(args))
    return Add, [pct_vec(args...)], partial_inference(Add, pct_vec(args...))
end


function e_class_reduction(::Type{Mul}, term::PCTVector)
    args = vcat(flatten_mul.(content(term))...)
    args = filter(t -> !is_one(t), args)
    n_negative = count(is_minus_one, args)
    args = filter(t -> !is_minus_one(t), args)
    n_negative % 2 == 1 && pushfirst!(args, constant(-1))
    any(is_zero, args) && return Constant, [0], I()
    isempty(args) && return Constant, [1], I()
    sort!(args)
    if length(args) == 1
        return typeof(first(args)), terms(first(args)), get_type(first(args))
    end
    return Mul, [pct_vec(args...)], partial_inference(Mul, pct_vec(args...))
end

function e_class_reduction(::Type{T}, from::PCTVector, summand::APN) where T <: Union{Contraction, Prod}
    isempty(content(from)) && return typeof(summand), [terms(summand)...], get_type(summand)
    is_zero(summand) && return Constant, [0], partial_inference(Constant, 0)
    is_one(summand) && T == Prod && return Constant, [1], partial_inference(Constant, 1)
    #= new_from = Vector{Var}()
    for t in content(from)
        !(t in new_from) && push!(new_from, t)
    end =#
    #= new_from, summand = renaming(new_from, summand) =#
    #= new_from = pct_vec(new_from...) =#
    new_from = from
    T, [new_from, summand], partial_inference(Sum, new_from, summand)
end

function e_class_reduction(::Type{T}, upper::PCTVector, lower::PCTVector, inner::R) where {T <: AbstractDelta, R <: APN}

    pair_sets = Vector{Set{APN}}()
    pairs = Vector{Pair{APN, APN}}()

    for (u, l) in zip(content(upper), content(lower))
        u == l && continue
        next_pair = Set([u, l])
        next_pair in pair_sets && continue
        push!(pair_sets, next_pair)
        push!(pairs , u=>l)
    end

    new_upper, new_lower = first.(pairs), last.(pairs)
    isempty(new_upper) && return R, terms(inner), get_type(inner)
     
    new_upper = pct_vec(new_upper...)
    new_lower = pct_vec(new_lower...)

    return T, [new_upper, new_lower, inner], partial_inference(T, new_upper, new_lower, inner)
end


function e_class_reduction(::Type{Conjugate}, term::T) where {T<:APN}
    t = get_type(term)
    if T == Mul
        sub_terms = pct_vec(map(conjugate, content(fc(term)))...)
        return Mul, [sub_terms], partial_inference(Mul, sub_terms)
    end
    if T == Constant
        new_const = fc(term)'
        return Constant, [new_const], partial_inference(Constant, new_const)
    end
    T == Conjugate && return typeof(fc(term)), terms(fc(term)), get_type(fc(term))
    t in [I(), R()] && return T, terms(term), get_type(term)
    return Conjugate, [term], get_type(term)
end


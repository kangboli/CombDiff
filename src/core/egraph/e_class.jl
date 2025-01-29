
"""
    e_class_reduction(T, terms)

Reduce a term to one of the canonical ones within is e-class.
"""
function e_class_reduction(::Type{T}, terms::Vararg) where {T<:APN}
    return T, collect(terms), partial_inference(T, terms...)
end

function e_class_reduction(::Type{Conjugate}, term::T) where {T<:APN}
    t = get_type(term)
    t in [N(), I(), R()] && return T, terms(term), get_type(term)
    process_type(::Type{Mul}) = Mul, [pct_vec(map(conjugate, content(get_body(term)))...)]
    process_type(::Type{Constant}) = Constant, [get_body(term)']
    process_type(::Type{T}) where {T<:Contraction} = T, [get_bound(term), conjugate(get_body(term))]
    function process_type(::Type{T}) where {T<:AbstractDelta}
        T, [upper(term), lower(term), conjugate(get_body(term))]
    end
    process_type(::Type{Conjugate}) = typeof(get_body(term)), terms(get_body(term))
    process_type(::Type{<:APN}) = Conjugate, [term]

    function inferenced_type(::Type{T}) where {T}
        S, terms = process_type(T)
        partial_inference(S, terms...)
    end
    inferenced_type(::Type{Conjugate}) = get_type(get_body(term))
    return process_type(T)..., inferenced_type(T)
end


function e_class_reduction(::Type{PrimitiveCall}, mapp::Var, args::PCTVector)
    get_type(mapp) == UndeterminedPCTType() && return PrimitiveCall, [mapp, args], UndeterminedPCTType()
    return PrimitiveCall, [mapp, args], partial_inference(PrimitiveCall, mapp, args)
end

function e_class_reduction(::Type{T}, bound::PCTVector, args::PCTVector, body::APN) where T <: AbstractLet
    if isempty(content(bound))
        return typeof(body), terms(body), partial_inference(typeof(body), terms(body)...)
    end

    return T, [bound, args, body], partial_inference(T, bound, args, body)
end

function e_class_reduction(::Type{Monomial}, base::T, power::APN) where {T<:APN}
    is_zero(base) && return Constant, [0], I()
    is_zero(power) && return Constant, [1], N()
    is_one(power) && return T, terms(base), get_type(base)
    if isa(base, Constant) && isa(power, Constant) # && !isa(get_body(base), Integer)
        new_const = [float(get_body(base))^get_body(power)]
        return Constant, new_const, partial_inference(Constant, new_const...)
    end

    if isa(base, Mul)
        sub_terms = content(get_body(base))
        i = findfirst(t -> isa(t, Constant), sub_terms)
        if i !== nothing
            new_body = pct_vec(monomial(sub_terms[i], power), monomial(mul(sub_terms[1:end.!=i]...), power))
            new_mul = mul(new_body...)
            return typeof(new_mul), terms(new_mul), get_type(new_mul)
        end
    end

    if isa(base, Monomial)
        new_terms = [base.base, mul(base.power, power)]
        return Monomial, new_terms, partial_inference(Monomial, new_terms...)
    end

    return Monomial, [base, power], partial_inference(Monomial, base, power)
end


#= function combine_maps(terms::Vector)
    map_dict, remaining_terms = Dict{Int, Vector{APN}}(), Vector{APN}()
    function process_term!(a::Map)
        map_dict[length(get_bound(a))] = push!(get(map_dict, length(get_bound(a)), []), a)
    end

    process_term!(a::APN) = push!(remaining_terms, a)
    map(process_term!, terms)

    function process_kv(v)
        vs = get_bound(v[1])
        have_common_names = all(i->name.(get_bound(v[i]))==name.(vs), 1:length(v))
        new_bound = have_common_names ? vs : pct_vec(map(var, 
        new_symbol(v...; num=length(vs), symbol=:_a), get_type.(vs))...)
        return pct_map(new_bound..., add([ecall(x, new_bound...) for x in v]...))
    end

    new_maps = [process_kv(v) for (_, v) in map_dict]
    return [remaining_terms..., new_maps...]
end =#

is_var_term(v::Var) = true
is_var_term(v::Constant) = true
is_var_term(v::Mul) = length(get_body(v)) == 2 && isa(first(get_body(v)), Constant)
is_var_term(v::APN) = false


function group_term!(a::Constant, term_dict)
    term_dict[constant(1)] = get_body(a) + get(term_dict, constant(1), 0)
end

function group_term!(a::Mul, term_dict)
    #= is_constant = group(t -> isa(t, Constant), content(get_body(a)))
    constant_term = get(is_constant, true, [constant(1)]) |> first
    rest = mul(get(is_constant, false, [])...)
    term_dict[rest] = get_body(constant_term) + get(term_dict, rest, 0) =#
    if isa(first(get_body(a)), Constant)
        c, rest... = content(get_body(a))
        rest = mul(rest...)
    else
        c, rest = constant(1), a
    end
    term_dict[rest] = get_body(c) + get(term_dict, rest, 0)
end
function group_term!(a::APN, term_dict)
    term_dict[a] = 1 + get(term_dict, a, 0)
end


flatten_add(a::APN) = [a]
flatten_add(a::Add) = vcat(flatten_add.(content(get_body(a)))...)

function e_class_reduction(::Type{Add}, term::PCTVector)
    new_terms = vcat(flatten_add.(content(term))...)
    d = group(t -> isa(t, Constant), new_terms)
    const_term = sum(map(get_body, get(d, true, [])), init=0) |> constant
    new_terms = filter(t -> !is_zero(t), [const_term, get(d, false, [])...])

    if count(a -> isa(a, Map), new_terms) > 1
        new_map = combine_maps(new_terms)
        return repack(new_map)
    end

    #= sort!(new_terms) =#
    length(new_terms) == 0 && return Constant, [0], I()
    length(new_terms) == 1 && return repack(first(new_terms))

    return Add, [pct_vec(new_terms...)], partial_inference(Add, pct_vec(new_terms...))
end


function e_class_reduction(::Type{T}, bound::PCTVector, summand::S) where {T<:Contraction,S<:APN}

    is_zero(summand) && return Constant, [0], partial_inference(Constant, 0)
    # is_one(summand) && T == Prod && return Constant, [1], partial_inference(Constant, 1)
    isempty(content(bound)) && return S, terms(summand), get_type(summand)
    if T == S
        new_bound = pct_vec(content(bound)..., content(get_bound(summand))...)
        return T, [new_bound, get_body(summand)], partial_inference(Sum, new_bound, get_body(summand))
    end

    if isa(summand, Map)
        body_summand, bound_summand = get_body(summand), get_bound(summand)
        new_sum = pct_sum(bound..., body_summand)
        return Map, [bound_summand, new_sum], partial_inference(Map, bound_summand, new_sum)
    end

    if S == Mul
        sub_terms = content(get_body(summand))
        i = findfirst(t -> isa(t, Constant), sub_terms)
        if i !== nothing
            new_body = pct_vec(sub_terms[i], make_node(T, bound, mul(sub_terms[1:end.!=i]...)))
            new_mul = mul(new_body...)
            return typeof(new_mul), terms(new_mul), get_type(new_mul)
        end
    end

    T, [bound, summand], partial_inference(Sum, bound, summand)
end

flatten_mul(a::Mul)::Vector{APN} = vcat(flatten_mul.(content(get_body(a)))...)
flatten_mul(a::APN)::Vector{APN} = [a]

function e_class_reduction(::Type{Mul}, term::PCTVector)
    
    args = vcat(flatten_mul.(content(term))...)

    is_constant = group(t -> isa(t, Constant), args)
    args_const = get(is_constant, true, [])
    prefactor = constant(prod(get_body.(args_const), init=1))
    args = get(is_constant, false, [])
    is_one(prefactor) || push!(args, prefactor)
    is_zero(prefactor) && return Constant, [0], I()
    #= args = [prefactor, ...] =#
    #= args = filter(t -> !is_one(t), args) =#
    #= any(is_zero, args) && return Constant, [0], I() =#
    isempty(args) && return Constant, [1], N()
    sort!(args)
    length(args) == 1 && return repack(first(args))

    # -1 ⋅ (a + b) -> - a - b. The e class itself needs to be able to do basic cancellations,
    # which is hard in factorized form.
    if length(args) == 2 && first(args) == constant(-1) && isa(last(args), Add)
        return repack(add([mul(constant(-1), t) for t in get_body(last(args))]...))
    end

    #= i = findfirst(t -> isa(t, AbstractDelta), args)
    if i !== nothing
        t = args[i]
        return repack(make_node(typeof(t), upper(t), lower(t), mul(get_body(t), args[1:end.!=i]...)))
    end =#

    return Mul, [pct_vec(args...)], partial_inference(Mul, pct_vec(args...))
end


flatten_comp(c::AbstractComp) = vcat(flatten_comp.(content(get_body(c)))...)
flatten_comp(c::APN) = [c]


"""
Taken from Permutation.jl
"""
function perm_sign(p::Vector)
    n = length(p)
    result = 0
    todo = trues(n)
    while any(todo)
        k = findfirst(todo)
        todo[k] = false
        result += 1 # increment element count
        j = p[k]
        while j != k
            result += 1 # increment element count
            todo[j] = false
            j = p[j]
        end
        result += 1 # increment cycle count
    end
    return isodd(result) ? -1 : 1
end

function operator_segment(v::Vector)
    i = findfirst(t -> is_annihilation(t) != is_annihilation(first(v)), v)
    i === nothing && return [v]
    return [v[1:i-1], operator_segment(v[i:end])...]
end

function operator_ordering(ops::Vector)
    vs = operator_segment(ops)
    result = []
    sign = 1
    for v in vs
        p = sortperm(v)
        append!(result, v[p])
        sign *= perm_sign(p)
    end
    return result, sign
end


function e_class_reduction(::Type{T}, v::PCTVector) where {T<:AbstractComp}
    length(v) == 1 && return repack(first(content(v)))
    subterms = vcat(flatten_comp.(content(v))...)

    #= if all(t -> is_creation(t) || is_annihilation(t), subterms)
        subterms, sign = operator_ordering(subterms)
        if sign == -1
            return repack(composite(fermi_scalar(constant(sign)), make_node(T, pct_vec(subterms...))))
        end
    end =#
    body = pct_vec(subterms...)
    return T, [body], partial_inference(T, body)
end
function e_class_reduction(::Type{DeltaNot}, lower::APN, upper::APN, body::APN)
    if lower == upper && base(get_type(lower)) == N()
        return constant(0)
    else
        if any(is_zero, [lower, upper])
            other = is_zero(upper) ? lower : upper
            if isa(other, Mul) && isa(first(get_body(other)), Constant) &&
               get_body(first(get_body(other))) < 0
                upper = mul(constant(-1), other)
                lower = constant(0)
            end
        end

        return DeltaNot, [lower, upper, body], partial_inference(DeltaNot, lower, upper, body)
    end
end

function e_class_reduction(::Type{Delta}, lower::APN, upper::APN, body::APN)
    if lower == upper && base(get_type(lower)) == N()
        return repack(body)
    else
        if any(is_zero, [lower, upper])
            other = is_zero(upper) ? lower : upper
            if isa(other, Mul) && isa(first(get_body(other)), Constant) &&
               get_body(first(get_body(other))) < 0
                upper = mul(constant(-1), other)
                lower = constant(0)
            end
        end

        return Delta, [lower, upper, body], partial_inference(Delta, lower, upper, body)
    end
end
is_inv(::Type{Exp}, ::Type{Log}) = true
is_inv(::Type{Log}, ::Type{Exp}) = true
is_inv(::Type{T}, ::Type{S}) where {T<:APN,S<:APN} = false

function e_class_reduction(::Type{T}, body::S) where {T<:Univariate,S<:APN}
    if is_inv(T, S)
        stripped = get_body(S)
        return typeof(strip), get_body(stripped), get_type(stripped)
    else
        return T, [body], partial_inference(T, body)
    end
end

function remove_dup_indicator(t_upper::APN, t_lower::APN, n::APN)
    set_terms(n, map(t -> remove_dup_indicator(t_upper, t_lower, t), terms(n))...)
end

function remove_dup_indicator(t_upper::APN, t_lower::APN, n::Indicator)
    upper(n) == t_upper && lower(n) == t_lower && return get_body(n) # duplicates in body have been removed if code gets here.
    set_terms(n, map(t -> remove_dup_indicator(t_upper, t_lower, t), terms(n))...)
end

remove_dup_indicator(::APN, ::APN, n::TerminalNode) = n

function e_class_reduction(::Type{Indicator}, t_upper::APN, t_lower::APN, body::T) where {T<:APN}

    t_lower == minfty() && return repack(body)
    t_lower == infty() && return Constant, [0], I()
    upper(get_type(t_lower)) == t_upper && return repack(body)

    t_upper == infty() && return repack(body)
    t_upper == minfty() && return Constant, [0], I()
    lower(get_type(t_upper)) == t_lower && return repack(body)

    is_zero(body) && return Constant, [0], I()

    if t_lower == lower(get_type(t_upper)) || t_upper == upper(get_type(t_lower))
        return repack(body)
    end

    #= body = remove_dup_indicator(t_upper, t_lower, body) =#
    #= println(verbose(t_lower))
    println(verbose(t_upper)) =#
    #= t_lower == constant(1) && base(get_type(t_upper)) == N() && return T, terms(body), partial_inference(T, terms(body)...) =#

    #= diff = add(upper, mul(constant(-1), lower))
    isa(zero_compare(diff), Union{NonNeg, IsPos}) && return T, [body], partial_inference(T, body)     =#
    return Indicator, [t_upper, t_lower, body], partial_inference(Indicator, t_upper, t_lower, body)
end

function repack(n::APN)
    return typeof(n), terms(n), get_type(n)
end

function e_class_reduction(::Type{VacExp}, body::T) where {T<:APN}
    T == FermiScalar && return repack(get_body(body))
    T <: AbstractComp || return VacExp, [body], partial_inference(VacExp, body)

    sub_terms = content(get_body(body))
    scalars, remains = tee(t -> isa(t, FermiScalar), sub_terms)
    isempty(scalars) && return VacExp, [body], partial_inference(VacExp, body)

    new_term = mul(map(get_body, scalars)..., vac_exp(composite(remains...)))
    return typeof(new_term), terms(new_term), get_type(new_term)
end

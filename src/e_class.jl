
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
    process_type(::Type{Delta}) = Delta, [lower(term), upper(term), conjugate(get_body(term))]
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

function e_class_reduction(::Type{S}, mapp::T, new_args::PCTVector) where {S<:AbstractCall,T<:APN}
    """
    f(let g = ...
        (g, q)
    end)

    let g = ...
        f(g, q)
    end
    """
    println(pretty(new_args))
    if typeof(new_args) == Let
        let_arg = new_args
        body = get_body(let_arg)
        error("ahah")
        new_map_var = var(first(new_symbol(mapp, let_arg;)), get_type(mapp))
        new_map = pct_map(new_map_var,
            pct_let(get_bound(let_arg)..., args(let_arg)...,
                call(new_map_var, body...)))

        result = evaluate(call(new_map, mapp))
        return e_class_reduction(typeof(result), terms(result)...)
        #= return typeof(result), terms(result), partial_inference(Let, terms(result)...) =#
    end

    """
    (let f = ...
        m ->  f(m) 
    end)(x) 

    (m -> let f = ...
        f(m)
    end)(x)
    """
    if T == Let
        body = get_body(mapp)
        new_vars = map(var, new_symbol(mapp; num=length(new_args)))
        new_map = pct_map(new_vars...,
            pct_let(get_bound(mapp)..., args(mapp)..., evaluate(call(body, new_vars...))))

        result = call(new_map, new_args...)
        return typeof(result), terms(result), partial_inference(Let, terms(result)...)
    end

    return S, [mapp, new_args...], partial_inference(S, mapp, new_args...)
end


function e_class_reduction(::Type{Monomial}, base::T, power::APN) where {T<:APN}
    is_zero(base) && return Constant, [0], I()
    is_zero(power) && return Constant, [1], N()
    is_one(power) && return T, terms(base), get_type(base)
    if isa(base, Constant) && isa(power, Constant)
        new_const = [get_body(base)^get_body(power)]
        return Constant, new_const, partial_inference(Constant, new_const)
    end
    return Monomial, [base, power], partial_inference(Monomial, base, power)
end

function combine_factors(terms::Vector)
    term_dict = Dict{APN,Number}()
    function process_term!(a::Constant)
        term_dict[constant(1)] = get_body(a) + get(term_dict, constant(1), 0)
    end
    function process_term!(a::Mul)
        is_constant = group(t -> isa(t, Constant), content(get_body(a)))
        constant_term = get(is_constant, true, [constant(1)]) |> first
        rest = mul(get(is_constant, false, [])...)
        term_dict[rest] = get_body(constant_term) + get(term_dict, rest, 0)
    end
    function process_term!(a::APN)
        #= println(typeof(a))
        println(hash(a)) =#
        term_dict[a] = 1 + get(term_dict, a, 0)
    end

    map(process_term!, terms)
    return [v == 1 ? k : mul(constant(v), k) for (k, v) in term_dict if v != 0]
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

flatten_add(a::APN) = [a]
flatten_add(a::Add) = vcat(flatten_add.(content(get_body(a)))...)

function e_class_reduction(::Type{Add}, term::PCTVector)
    new_terms = vcat(flatten_add.(content(term))...)
    d = group(t -> isa(t, Constant), new_terms)
    const_term = sum(map(get_body, get(d, true, [])), init=0) |> constant
    new_terms = filter(t -> !is_zero(t), [const_term, get(d, false, [])...])
    new_terms = combine_factors(new_terms)

    #= if count(a->isa(a, Map), new_terms) > 1
        new_terms = combine_maps(new_terms)
    end =#

    sort!(new_terms)
    length(new_terms) == 0 && return Constant, [0], I()
    length(new_terms) == 1 && return typeof(first(new_terms)), terms(first(new_terms)), get_type(first(new_terms))

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

    T, [bound, summand], partial_inference(Sum, bound, summand)
end

flatten_mul(a::Mul) = vcat(flatten_mul.(content(get_body(a)))...)
flatten_mul(a::APN) = [a]

function e_class_reduction(::Type{Mul}, term::PCTVector)
    args = vcat(flatten_mul.(content(term))...)
    is_constant = group(t -> isa(t, Constant), args)
    args_const = get(is_constant, true, [])
    args = [constant(prod(get_body, args_const, init=1.0)), get(is_constant, false, [])...]
    args = filter(t -> !is_one(t), args)
    any(is_zero, args) && return Constant, [0], I()
    isempty(args) && return Constant, [1], N()
    sort!(args)
    if length(args) == 1
        return typeof(first(args)), terms(first(args)), get_type(first(args))
    end
    return Mul, [pct_vec(args...)], partial_inference(Mul, pct_vec(args...))
end


flatten_comp(c::Composition) = vcat(flatten_comp.(content(get_body(c)))...)
flatten_comp(c::APN) = [c]

function e_class_reduction(::Type{Composition}, term::PCTVector)
    body = pct_vec(vcat(flatten_comp.(content(term))...)...)
    return Composition, [body], partial_inference(Composition, body)
end

function e_class_reduction(::Type{Delta}, lower::APN, upper::APN, body::APN)
    if lower == upper
        return typeof(body), terms(body), get_type(body)
    else
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

function e_class_reduction(::Type{PCTVector}, elements::Vararg)
    i = findall(t -> isa(t, Let), elements)
    isempty(i) && return PCTVector, elements, partial_inference(PCTVector, elements...)
    length(i) > 1 && error("only one let is currently supported for unwrapping let expression in PCT vectors")
    i = first(i)
    t_let, rest = elements[i], elements[1:end.!=i]
    new_body = Vector{APN}(map(var, new_symbol(elements...; num=length(elements)), get_type.(elements)))
    new_body[i] = get_body(t_let)
    interior = pct_let(
        get_bound(t_let)...,
        args(t_let)...,
        new_body...
    )

    result = interior
    if length(new_body) > 1
        result = evaluate(call(pct_map(new_body[1:end.!=i]...,
                interior), rest...))
    end

    return typeof(result), terms(result), get_type(result)
end

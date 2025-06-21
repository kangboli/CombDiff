neighbor_registry = Dict{Type,Vector}()

is_deadend!(::TerminalNode, _) = true
function is_deadend(n::APN, settings)
    return objectid(n) in settings[:deadend]
end

tag_deadend!(::TerminalNode, _) = nothing
function tag_deadend!(n::APN, settings)
    push!(settings[:deadend], objectid(n))
    for t in terms(n)
        untag_deadend!(t, settings)
    end
end

untag_deadend!(::TerminalNode, _) = nothing
function untag_deadend!(n::APN, settings)
    delete!(settings[:deadend], objectid(n))
    for t in terms(n)
        untag_deadend!(t, settings)
    end
end

"""
Equivalent sets for PCT nodes.
"""

struct NeighborList
    nodes::Vector{APN}
    directed::Vector{Bool}
    names::Vector{String}
end

NeighborList() = NeighborList(Vector{APN}(), Vector{Bool}(), Vector{String}())
Base.lastindex(n::NeighborList) = length(nodes(n))
nodes(n::NeighborList) = n.nodes
directed(n::NeighborList) = n.directed
names(n::NeighborList) = n.names

function Base.push!(n::NeighborList, node; dired=false, name="Unknown")
    push!(nodes(n), node)
    push!(directed(n), dired)
    push!(names(n), name)
    return n
end

Base.length(n::NeighborList) = length(nodes(n))

Base.iterate(n::NeighborList) = length(n) > 0 ? (n[1], 2) : nothing
Base.iterate(n::NeighborList, state::Integer) = state > length(n) ? nothing : (n[state], state + 1)

function Base.getindex(n::NeighborList, i::Integer)
    return (nodes(n)[i], directed(n)[i])
end

function Base.append!(n_1::NeighborList, n_2::NeighborList)
    append!(nodes(n_1), nodes(n_2))
    append!(directed(n_1), directed(n_2))
    append!(names(n_1), names(n_2))
    return n_1
end

function pretty(n::NeighborList)
    join(map((name, t) -> "$(name): $(pretty(t))", names(n), nodes(n)), "\n")
end

function Base.show(io::IO, ::MIME"text/plain", n::NeighborList)
    print(io, pretty(n))
end

function latex(n::NeighborList)
    join(map((name, t) -> "$(name): $(latexstring(latex(t)))", names(n), nodes(n)), "\n")
end

function Base.show(io::IO, ::MIME"text/latex", n::NeighborList)
    print(io, latex(n))
end

neighbors(::Union{Var,Constant,FieldOperators}; _...) = NeighborList()

function sub_neighbors(c::AbstractCall; settings=default_settings())
    result = NeighborList()
    a = args(c)

    for i in 1:length(a)
        neighbor_list = neighbors(a[i], settings=settings)
        for (t, d, n) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content(c, mapp(c), set_i(a, i, t)); dired=d, name=n)
        end
    end

    return result
end

#= function k_out_neighbors(p::PrimitiveCall)
    result = NeighborList()
    isa(mapp(p), AbstractPullback) || return result
    zs..., k = content(args(p))
    if isa(get_type(k), ElementType)
        push!(result, mul(call(mapp(p), zs..., constant(1)), k);
            dired=true, name="k_out")
    end
    return result
end =#
function is_pullback_of_univariate(p::AbstractPullback)
    isa(get_body_type(get_type(get_body(p))), ElementType)
end

function delta_out_linear(c::AbstractCall)
    result = NeighborList()
    i = findfirst(t -> isa(t, Delta), content(args(c)))
    i === nothing && return result
    d = args(c)[i]
    m = if length(args(c)) == 1
        mapp(c)
    else
        k = var(first(new_symbol(c)), get_type(d))
        pct_map(k, call(mapp(c), set_i(args(c), i, k)))
    end

    is_linear(m) || return result

    push!(result, delta(lower(d), upper(d), ecall(m, get_body(d))); dired=true, name="delta_out_linear")

    return result
end


function delta_out_pullback_neighbors(c::AbstractCall)
    result = NeighborList()
    isa(mapp(c), AbstractPullback) || return result
    k_type = get_body_type(get_type(get_body(mapp(c))))
    zs..., k = content(args(c))
    isa(k, Delta) || return result
    if isa(k_type, VecType)
        isa(get_type(k), SplatType) || return result
        get_body_type(get_type(k)) == k_type || return result
    end
    push!(result, delta(upper(k), lower(k), call(mapp(c), zs..., get_body(k))); dired=true, name="delta_out_pullback")
end

"""
𝒫 (z -> f(z)) (t, let p = g(q)
    p * k
end)

(t -> let p = g(q)
    t (p * k)
end)(k -> P(z -> f(z))(t, k))

𝒫 (z -> f(z)) (p, let p = g(q)
    p * k
end)
"""
function let_out_pullback(p::AbstractCall)
    result = NeighborList()
    isa(mapp(p), PrimitivePullback) || return result
    inner_map = get_body(mapp(p))
    map_output_type = get_body_type(get_type(inner_map))
    isa(map_output_type, VecType) && return result
    new_args..., let_term = content(args(p))
    if isa(let_term, Let)

        t = var(first(new_symbol(p)), MapType(VecType([get_type(let_term)]), get_type(p)))
        new_let = pct_map(t, pct_let(get_bound(let_term)..., args(let_term)...,
            call(t, get_body(let_term))))

        k = var(first(new_symbol(p, t)), get_type(let_term))
        new_map = pct_map(k, evaluate(call(mapp(p), new_args..., k)))

        push!(result, eval_all(call(new_let, new_map)); dired=true, name="let_out_pullback")
    elseif isa(let_term, Sum) && isa(get_body(let_term), Let)
        sum_let = let_term
        let_term = get_body(sum_let)

        t = var(first(new_symbol(p)), MapType(VecType([get_type(sum_let)]), get_type(p)))
        new_sum_let = pct_map(t,
            pct_sum(get_bound(sum_let)...,
                pct_let(get_bound(let_term)..., args(let_term)...,
                    call(t, get_body(let_term)))))

        k = var(first(new_symbol(p, t)), get_type(sum_let))
        new_map = pct_map(k, evaluate(call(mapp(p), new_args..., k)))

        push!(result, eval_all(call(new_sum_let, new_map)); dired=true, name="sum_let_out_pullback")

    end
    return result
end

"""
(f(b))(a, let
    b = c
    b
end)

((x, y) -> let b = c
    (x)(y, b)
end)(f(b), a)

let e = c
    (f(b))(a, e)
end

"""
function let_out_call(p::AbstractCall)
    result = NeighborList()
    i = findfirst(t -> isa(t, Let), content(args(p)))
    i === nothing && return result
    lt = args(p)[i]

    new_vars = map(var, new_symbol(p; num=length(args(p))), [get_type(mapp(p)), get_type.(remove_i(args(p), i))...])

    var_args = Vector{APN}(new_vars[2:end])
    insert!(var_args, i, get_body(lt))
    new_let = call(pct_map(new_vars..., pct_let(
            get_bound(lt)..., args(lt)...,
            call(first(new_vars), var_args...)
        )), mapp(p), remove_i(args(p), i)...)
    push!(result, eval_all(new_let); dired=true, name="let_out_call")

    return result
end

function meta_prop_neighbors(c)
    result = NeighborList()
    get(meta(get_type(mapp(c))), :off_diag, false) || return result

    t = first(args(c))
    for r in args(c)
        r == t || return result
    end
    push!(result, constant(0); dired=true, name="off_diag")
    return result
end


desplat(s::Splat) = get_body(s)
desplat(s::APN) = set_terms(s, map(desplat, terms(s))...)
desplat(s::TerminalNode) = s
function surface_vec(n::Delta)
    body = surface_vec(get_body(n))
    isa(body, PCTVector) || return n
    return pct_vec([delta(upper(n), lower(n), b) for b in body]...)
end
surface_vec(v::PCTVector) = v
surface_vec(n::APN) = n

function delta_splat_call(p::T) where {T<:AbstractCall}
    result = NeighborList()
    T == Call || return result
    isa(mapp(p), Map) || return result

    any(a -> isa(get_type(a), SplatType), args(p)) || return result
    new_args = Vector{APN}()
    splatted = false
    for a in args(p)
        if isa(get_type(a), SplatType)
            v = surface_vec(desplat(a))
            if isa(v, PCTVector)
                splatted = true
                append!(new_args, v)
            else
                push!(new_args, a)
            end
        else
            push!(new_args, a)
        end
    end
    splatted || return result
    new_node = ecall(mapp(p), new_args...)
    push!(result, new_node; dired=true, name="delta_splat_call")
    return result
end

function bypass_eval(c::AbstractCall)
    result = NeighborList()
    m = mapp(c)
    isa(m, Map) || return result
    free = get_free(get_body(m))
    any(b -> b in free, get_bound(m)) && return result
    push!(result, get_body(m); dired=true, name="bypass_eval")
    return result
end

#= function apply_symmetry(indices, op)
    # Apply the permutation.
    new_term = set_content(c, mapp(c), args(c)[collect(indices)])
    # Apply the symmetry operation.
    op == :conj && return conjugate(new_term)
    op == :id && return new_term
    op == :neg && return mul(constant(-1), new_term)
    if op in [:ineg, :inegc]
        new_args = []
        for (i, a) in enumerate(content(args(c)))
            if i in indices
                push!(new_args, mul(constant(-1), a))
            else
                push!(new_args, a)
            end
        end
        negated = set_content(c, mapp(c), pct_vec(new_args...))
        if op == :ineg
            return negated
        else
            return conjugate(negated)
        end
    end
    #= op == :inegc && error("Not yet properly implemented") =#
    #= return conjugate(set_content(c, mapp(c),
        [mul(constant(-1), t) for t in args(c)[collect(indices)]])) =#
    return new_term
end

for (indices, op) in symmetries(get_type(mapp(c)))
    op == :neg || continue
    args(c) == args(c)[collect(indices)] || continue
    push!(result, constant(0); dired=true, name="forbidden_symmetry")
    return result
end =#

neighbor_registry[AbstractCall] = [
    delta_out_pullback_neighbors,
    delta_out_linear,
    let_out_pullback,
    let_out_call,
    delta_splat_call,
    meta_prop_neighbors,
    bypass_eval,
]

function neighbors(c::AbstractCall; settings=default_settings())
    result = NeighborList()

    for edge in neighbor_registry[AbstractCall]
        append!(result, edge(c))
    end

    append!(result, sub_neighbors(c; settings=settings))

    settings[:symmetry] || return result

    for sym in symmetries(get_type(mapp(c)))
        #= new_term = apply_symmetry(indices, op) =#
        new_term = ecall(ecall(sym, mapp(c)), args(c)...)
        if new_term == mul(constant(-1), c)
            push!(result, constant(0); name="forbidden_symmetry")
        else
            push!(result, new_term; name="symmetry")
        end
    end

    return result
end

function neighbors(::PrimitivePullback; _...)
    return NeighborList()
end


"""
Currently, we do not extract powers. For example, `i^2 + i` will be not
factored into `i*(i+1)`.
"""
function gcd(a::APN, b::APN)
    a_rem = Vector{APN}()
    b_rem = isa(b, Mul) ? copy(content(get_body(b))) : [b]
    c = Vector{APN}()

    for t in (isa(a, Mul) ? content(get_body(a)) : [a])
        i = findfirst(k -> k == t, b_rem)
        if i === nothing
            push!(a_rem, t)
        else
            push!(c, t)
            deleteat!(b_rem, i)
        end
    end

    fill_one(x) = isempty(x) ? Set([make_node(Constant, 1)]) : x
    a_rem, b_rem, c = map(fill_one, (a_rem, b_rem, c))

    node_bound_set(s) = length(s) > 1 ? mul(s...) : first(collect(s))
    return map(node_bound_set, (a_rem, b_rem, c))
end

function gcd_neighbors(terms::Vector)
    result = NeighborList()
    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            x_rem, y_rem, common = gcd(x, y)

            isa(common, Constant) && continue
            #= is_one(common) && continue
            is_minus_one(common) && continue =#
            push!(result, add(mul(common, add(x_rem, y_rem)),
                    terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]...); name="gcd", dired=true)
        end
    end
    return result
end

function add_delta_neighbors(terms::Vector)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Delta) && isa(y, Delta) || continue
            Set([upper(x), lower(x)]) == Set([upper(y), lower(y)]) || continue
            new_delta = delta(lower(x), upper(x), add(last(content(x)), last(content(y))))
            new_terms = terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]
            push!(result, add(new_delta, new_terms...); dired=true, name="add_delta")
        end
    end
    return result
end

function sub_neighbors(n::Union{Add,Mul}; settings=default_settings())
    result = NeighborList()
    body = get_body(n)
    p = sortperm(content(body), by=t -> is_deadend(t, settings))

    for i = p
        neighbor_list = neighbors(body[i]; settings=settings)
        for (t, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content(n, set_i(body, i, t)); dired=d, name=s)
            d && return result
        end
        any(directed(neighbor_list)) || tag_deadend!(body[i], settings)
    end

    return result
end

#= function combine_map_neighbors(terms::Vector)
    result = NeighborList()
    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Map) && isa(y, Map) || continue
            length(get_bound(x)) == length(get_bound(y)) || continue
            all(i -> get_type(get_bound(x)[i]) == get_type(get_bound(y)[i]), 1:length(get_bound(x))) || continue

            new_bound = get_bound(x) == get_bound(y) ? get_bound(x) :
                        pct_vec(map(var, range.(get_bound(x)), new_symbol(x, y; num=length(get_bound(x)), symbol=:_a), get_type.(get_bound(x))))

            new_map = pct_map(new_bound..., add(ecall(x, new_bound...), ecall(y, new_bound...)))

            push!(result, add(new_map, terms[(k->k != i && k != j).(1:end)]...); dired=true, name="combine_map")
        end
    end

    return result
end =#

function combine_maps(terms::Vector)
    map_dict, remaining_terms = Dict{Int,Vector{APN}}(), Vector{APN}()
    function process_term!(a::Map)
        map_dict[length(get_bound(a))] = push!(get(map_dict, length(get_bound(a)), []), a)
    end

    process_term!(a::APN) = push!(remaining_terms, a)
    map(process_term!, terms)

    function process_kv(v)
        vs = get_bound(v[1])
        have_common_names = all(i -> name.(get_bound(v[i])) == name.(vs), 1:length(v))
        new_bound = have_common_names ? vs : pct_vec(map(var,
            new_symbol(v...; num=length(vs), symbol=:_a), get_type.(vs))...)
        return pct_map(new_bound..., add([ecall(x, new_bound...) for x in v]...))
    end

    new_maps = [process_kv(v) for (_, v) in map_dict]
    return [remaining_terms..., new_maps...]
end

function combine_factors(a)
    result = NeighborList()
    terms = content(get_body(a))
    term_dict = Dict{APN,Number}()

    for t in terms
        group_term!(t, term_dict)
    end
    new_terms = if isa(get_type(a), ElementType)
        [v == 1 ? k : mul(constant(v), k) for (k, v) in term_dict if v != 0]
    else
        [v == 1 ? k : composite(fermi_scalar(constant(v)), k) for (k, v) in term_dict if v != 0]
    end

    new_add = add(new_terms...)
    new_add == a && return result
    push!(result, new_add; dired=true, name="combine_factors")

    return result
end


function neighbors(a::Add; settings=default_settings())
    result = NeighborList()
    time = @elapsed begin
        terms = content(get_body(a))

        #= if count(t -> isa(get_type(t), MapType), content(get_body(a))) > 1
            new_add = add(combine_maps(content(get_body(a)))...)
            push!(result, new_add; dired=true, name="combine_map")
        end =#
        #= append!(result, combine_map_neighbors(terms)) =#
        sub_result = sub_neighbors(a; settings=settings)
        #= for (i, t) in enumerate(nodes(sub_result))
            isa(t, Add) && length(content(get_body(t))) == length(content(get_body(a))) && continue
            directed(sub_result)[i] = true
        end =#
        append!(result, sub_result)
        let_time = @elapsed append!(result, let_out_mul_add(a))

        settings[:full_log] && println("Let time: $(let_time)")
    end
    settings[:full_log] && println("exploring add: $(time)")
    any(directed(result)) && return result
    time += @elapsed begin
        append!(result, add_delta_neighbors(terms))
        settings[:combine_factors] && append!(result, combine_factors(a))

        settings[:gcd] && append!(result, gcd_neighbors(terms))
    end
    settings[:full_log] && println("exploring add: $(time)")
    return result
end

"""
x^a * x^b -> x^(a + b)
"""
function mul_add_neighbors(terms::Vector)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            base(x) == base(y) || continue

            new_monomial = monomial(base(x), add(power(x), power(y)))
            new_terms = terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]
            push!(result, mul(new_monomial, new_terms...); name="mul_to_power", dired=true)
        end
    end
    return result
end

function swallow_neighbors(m::R) where {R<:Union{Mul,Composition}}
    result = NeighborList()
    terms = get_body(m)
    for (i, x) in enumerate(content(terms))
        T = typeof(x)
        T <: AbstractDelta || continue
        #= rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))] =#
        new_r = make_node(R, set_i(terms, i, get_body(x)))
        push!(result, make_node(T, upper(x), lower(x), new_r); dired=true, name="swallow_$(lowercase(string(R)))")
    end
    return result
end

"""
x ⋅ 𝕀(1, 2, y) -> 𝕀(1, 2, y ⋅ x)
"""
function indicator_swallow_neighbors(terms)
    result = NeighborList()
    for (i, x) in enumerate(terms)
        isa(x, Indicator) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, indicator(upper(x), lower(x), mul(get_body(x), rem_terms...)); dired=true, name="indicator_swallow_mul")
    end
    return result
end

function mul_product_neighbors(terms)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Prod) && isa(y, Prod) && get_type(get_bound(x)) == get_type(get_bound(y)) || continue
            z = var(first(new_symbol(x, y)), get_type(get_bound(x)))
            new_prod = make_node(Prod, z, mul(subst(get_body(x), get_bound(x), z), subst(get_body(y), get_bound(y), z)))
            new_terms = terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]
            push!(result, mul(new_prod, new_terms...); name="mul_product")
        end
    end
    return result
end

function dist_neighbors(terms::Vector)
    result = NeighborList()
    for (i, t) in enumerate(terms)
        isa(t, Add) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, add(content(map(n -> mul(rem_terms..., n), get_body(t)))...); name="dist")
    end
    return result
end

#= function prod_in_neighbors(terms)
    result = NeighborList()
    for (i, t) in enumerate(terms)
        isa(t, Sum) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]

        if contains_name(rem_terms..., name(get_bound(t)))
            t = set_ff(t, first(new_symbol(rem_terms..., t)))
        end

        push!(result, set_content(t, mul(get_body(t), rem_terms)); name="prod_in")
    end
    return result
end =#

function prod_const_neighbors(terms)
    result = NeighborList()
    constants = filter(t -> isa(t, Constant), terms)
    nonconstants = filter(t -> !isa(t, Constant), terms)
    length(constants) > 1 || return result

    new_const = make_node(Constant, prod(get_body, constants))
    new_term = is_one(new_const) ? mul(nonconstants...) :
               mul(new_const, nonconstants...)
    push!(result, new_term; dired=true, name="prod_const")
    return result
end

function neighbors(m::Mul; settings=default_settings())

    result = NeighborList()
    time = @elapsed begin
        terms = content(get_body(m))
        append!(result, mul_add_neighbors(terms))
        #= settings[:clench_sum] || append!(result, relax_sum(terms)) =#
        settings[:clench_delta] || append!(result, swallow_neighbors(m))
        append!(result, indicator_swallow_neighbors(terms))
        #= append!(result, mul_expand_const_neighbors(m)) =#
        append!(result, let_out_mul_add(m))
        settings[:expand_mul] && append!(result, mul_expand_neighbors(m))
        #= append!(result, mul_product_neighbors(terms)) =#
        #= append!(result, dist_neighbors(terms)) =#
        #= append!(result, prod_const_neighbors(terms)) =#
        append!(result, sub_neighbors(m; settings=settings))
    end
    settings[:full_log] && println("exploring mul $(time)")
    return result
end

function map_let_out(s::Map; settings=default_settings())
    result = NeighborList()
    body = get_body(s)
    isa(get_body(s), Let) || return result
    all(t -> isa(get_type(t), ElementType) && base(get_type(t)) == N(), content(get_bound(s))) || return result
    interior, exterior = [], []
    for b in get_bound(s)
        free_let = union!(get_free(get_bound(body)), get_free(args(body)))
        if any(t -> get_body(t) == get_body(b), free_let)
            push!(exterior, b)
        else
            push!(interior, b)
        end
    end
    length(interior) == length(get_bound(s)) || return result

    constructor = pct_map
    new_term = pct_let(get_bound(body)..., args(body)...,
        constructor(interior..., get_body(body)))
    if !isempty(exterior)
        new_term = constructor(exterior..., new_term)
    end
    push!(result, new_term; dired=true, name="let_out_map")
    return result
end

function delta_out_map(m::Map; _...)
    result = NeighborList()
    delta_term = get_body(m)
    D = typeof(get_body(m))
    D <: AbstractDelta || return result

    delta_map = make_node(D, upper(delta_term), lower(delta_term),
        pct_map(get_bound(m)..., get_body(delta_term)))

    push!(result, delta_map; dired=true, name="delta_out_map")
    return result

end

neighbor_registry[Map] = [
    map_let_out,
    sub_neighbors,
    #= delta_out_map =#
]

function neighbors(m::Map; settings=default_settings())

    result = NeighborList()
    time = @elapsed begin
        if isa(get_body(m), Contraction)
            settings = custom_settings(:skip_self_as_intermediate => true; preset=settings)
        end

        for edge in neighbor_registry[Map]
            append!(result, edge(m; settings=settings))
        end
        #= append!(result, sub_neighbors(m; settings=settings))
        append!(result, map_let_out(m)) =#
    end
    settings[:full_log] && println("exploring map $(time)")
    return result
end

function add_mul_neighbors(m::Monomial)
    result = NeighborList()
    b, p = base(m), power(m)
    isa(p, Add) || return result
    terms = content(get_body(p))
    for (i, t) in enumerate(terms)
        rem_terms = terms[1:end.!=i]
        push!(result, mul(monomial(b, t), monomial(b, add(rem_terms...))); name="add_mul")
    end
    return result
end



function neighbors(m::Monomial; settings=default_settings())
    result = NeighborList()
    b, p = base(m), power(m)

    isa(p, Sum) && push!(result, pct_product(get_bound(p)..., monomial(b, get_body(p))); name="sum_prod")
    #= append!(result, add_mul_neighbors(m)) =#
    append!(result, sub_neighbors(m, settings=settings))
    return result
end

function sum_sym_neighbors(s::Sum)
    result = NeighborList()

    for v in content(get_bound(s))
        symmetric(v) || continue
        push!(result, pct_sum(content(get_bound(s))..., subst(get_body(s), v, mul(constant(-1), v))); name="sum_sym")
    end

    return result
end

"""
sum(i, k) = N ⋅ k
"""
function sum_mul_neighbors(s::Sum)
    result = NeighborList()

    i_rem, factors = Vector{APN}(), Vector{APN}()

    for v in content(get_bound(s))
        contains_name(get_body(s), name(v)) && continue
        if isa(get_type(v), Domain)
            push!(factors, add(constant(1), upper(get_type(v)), mul(constant(-1), lower(get_type(v)))))
        else
            push!(i_rem, v)
        end
    end

    isempty(factors) && return result

    if isempty(i_rem)
        push!(result, mul(factors..., get_body(s)); dired=true, name="sum_mul")
    else
        push!(result, mul(factors..., pct_sum(i_rem..., get_body(s))); dired=true, name="sum_mul")
    end

    return result
end

function quick_solve(lhs::T, rhs::APN, v::Var) where {T<:APN}
    if T == Var
        name(lhs) == name(v)
    end
end

"""
sum(j, delta(i, j+k, A(i, j, k)))
sets j -> i - k

TODO: Clean up this mess
"""
function contract_delta_neighbors(s::Sum)
    result = NeighborList()
    d = get_body(s)
    isa(d, Delta) || return result

    new_bound = pct_vec(sort(content(get_bound(s)), by=t -> startswith(string(name(t)), "_"), rev=true)...)
    for (i, v) in enumerate(new_bound)
        contractable(expr::APN, s::Symbol)::Bool = false
        contractable(expr::Var, s::Symbol)::Bool = name(expr) == s
        function contractable(expr::Mul, s::Symbol)::Bool
            p = mul(expr, constant(-1))
            isa(p, Var) && contractable(p, s)
        end
        contractable(expr::Add, s::Symbol)::Bool = any(t -> contractable(t, s), get_body(expr))
        #= is_contractable(v) != isempty(range(v)) && error("bug alert! mismatch $(name(v)): $(range(v))") =#
        is_contractable(v) || continue
        #= isempty(range(v)) || continue =#
        indices = content(remove_i(new_bound, i))

        this, other = if contractable(upper(d), name(v))
            upper(d), lower(d)
        elseif contractable(lower(d), name(v))
            lower(d), upper(d)
        else
            continue
        end

        replacement = other
        if isa(this, Var)
            replacement = other
        elseif isa(this, Add)
            i = findfirst(t -> contains_name(t, name(v)), content(get_body(this)))
            v_term = get_body(this)[i]
            if isa(v_term, Var)
                replacement = add([mul(constant(-1), t) for t in content(get_body(this))]...)
                replacement = add(other, v, replacement)
            elseif isa(v_term, Mul) && first(get_body(v_term)) == constant(-1)
                length(get_body(v_term)) == 2 || error("delta with too complicated subscripts are not yet supported")
                replacement = subtract(add(this, v), other)
            end
        else
            #= mul(constant(-1), this) =#
            error("Not yet implemented")
        end
        new_summand = subst(get_body(d), v, replacement)
        if isa(get_type(v), ElementType)
            new_indicator = indicator(other, upper(get_type(v)), lower(get_type(v)), other, new_summand)
            new_sum = pct_sum(indices..., new_indicator)
        else
            new_sum = pct_sum(indices..., new_summand)
        end

        push!(result, new_sum; dired=true, name="contract_delta")
    end

    return result
end

"""
sum(i, j, k ⋅ x(i) ⋅ y(j)) -> k ⋅ sum(i, x(i) ⋅ sum(j, y(j)))
"""
function clench_sum(s::Sum)
    result = NeighborList()

    summand = get_body(s)
    if isa(summand, Mul)
        for (i, v) in enumerate(content(get_bound(s)))
            interior, exterior = Vector{APN}(), Vector{APN}()

            for t in content(get_body(summand))
                target = contains_name(t, name(v)) ? interior : exterior
                push!(target, t)
            end
            isempty(exterior) && continue
            new_v = remove_i(get_bound(s), i)
            new_sum = pct_sum(content(new_v)..., mul(exterior..., pct_sum(get_bound(s)[i], mul(interior...))))
            push!(result, new_sum; dired=false, name="sum_clench")
        end
    end

    return result
end


function obvious_clench(s::Sum)
    result = NeighborList()

    summand = get_body(s)
    if isa(summand, Mul)
        interior, exterior = Vector{APN}(), Vector{APN}()

        for t in content(get_body(summand))
            target = any(v -> contains_name(t, name(v)), content(get_bound(s))) ? interior : exterior
            push!(target, t)
        end

        isempty(exterior) && return result

        new_sum = mul(exterior..., pct_sum(content(get_bound(s))..., mul(interior...)))
        push!(result, new_sum; dired=true, name="obvious_clench")
    end


    return result
end

function sum_out_primitive_pullback(s::Sum)
    result = NeighborList()
    summand = get_body(s)
    isa(summand, AbstractCall) && isa(mapp(summand), PrimitivePullback) || return result
    k_type = get_body_type(get_type(get_body(mapp(summand))))
    isa(k_type, VecType) && return result
    for b in get_bound(s)
        contains_name(mapp(summand), name(b)) && return result
    end
    new_pullback = primitive_call(mapp(summand), args(summand)[1:end-1]...,
        pct_sum(get_bound(s)..., last(args(summand))))
    push!(result, new_pullback; dired=true, name="pullback_sum_out")
    return result
end

function sum_out_linear_op(s::Sum)
    result = NeighborList()
    summand = get_body(s)
    (isa(summand, AbstractCall) ||
     (isa(summand, Conjugate) &&
      isa(get_body(summand), AbstractCall))) || return result
    linear(get_type(mapp(summand))) && length(args(summand)) == 1 || return result
    new_sum = call(mapp(summand), pct_sum(get_bound(s)..., first(args(summand))))

    push!(result, new_sum; dired=true, name="linear_sum_out")
    return result
end


"""
sum(i, i * sum(j, A(i, j) * j)) = sum(j, j * sum(i, i * A(i, j)))
This is broken. Do not use.
"""
function sum_exchange(s::Sum)
    result = NeighborList()

    mul_term = get_body(s)
    isa(mul_term, Mul) || return result
    index_sum = findfirst(t -> isa(t, Sum), content(get_body(mul_term)))
    index_sum === nothing && return result
    sum_term = content(get_body(mul_term))[index_sum]
    other_terms = content(get_body(mul_term))[1:end.!=index_sum]
    for (i, term_i) in enumerate(content(get_bound(s)))
        function can_pullout(t::APN)
            !contains_name(t, name(term_i))
        end

        inner_terms = isa(get_body(sum_term), Mul) ? content(get_body(get_body(sum_term))) : [get_body(sum_term)]
        exterior = filter(can_pullout, inner_terms)
        interior = filter(t -> !can_pullout(t), inner_terms)
        isempty(exterior) && continue

        function require_rename(t::T) where {T<:Var}
            for o in other_terms
                free, _ = free_and_dummy(o)
                name(t) in name.(free) && return true
            end
            return false
        end

        symbols = new_symbol(s, num=count(require_rename, content(get_bound(sum_term))), symbol=:_s)
        new_ff = Vector{Var}()
        for t in content(get_bound(sum_term))
            if require_rename(t)
                new_var = var(pop!(symbols), get_type(t))
                push!(new_ff, new_var)
                update_term(s) = subst(s, t, new_var)
                exterior = update_term.(exterior)
            else
                push!(new_ff, t)
            end
        end

        new_sum = pct_sum(content(get_bound(s))[1:end.!=i]..., new_ff...,
            mul(exterior..., pct_sum(term_i, mul(other_terms..., interior...))))
        push!(result, new_sum; name="sum_exchange")
    end
    return result
end



function sum_out_delta(s::Sum)
    result = NeighborList()
    d = get_body(s)
    isa(d, Delta) || return result
    for (i, v) in enumerate(content(get_bound(s)))
        (contains_name(upper(d), name(v)) || contains_name(lower(d), name(v))) && continue
        new_v = remove_i(get_bound(s), i)
        new_sum = pct_sum(content(new_v)..., delta(upper(d), lower(d), pct_sum(get_bound(s)[i], get_body(d))))
        push!(result, new_sum; dired=true, name="sum_out_delta")
    end

    return result
end



"""
sum(i, sum(j, x(i, j))) -> sum((i, j), x(i, j))
"""
function sum_merge_neighbors(s::Sum)
    result = NeighborList()
    isa(get_body(s), Sum) || return result

    new_indices = pct_vec(vcat(content(get_bound(s)), content(get_bound(get_body(s))))...)
    push!(result, pct_sum(content(new_indices)..., get_body(get_body(s))); dired=true, name="sum_merge")

    return result
end

function find_shift(i::T, n::APN) where {T<:Var}
    vcat([find_shift(i, t) for t in content(n)]...)
end

function find_shift(i::T, a::Add) where {T<:Var}
    rest = collect(filter(t -> t != i, content(get_body(a))))
    num = length(content(get_body(a))) - length(rest)
    num > 0 || return invoke(find_shift, Tuple{T,APN}, i, a)
    num > 1 && error("Unable to do multishift")
    return [add(rest...)]
end

function find_shift(::T, ::S) where {T<:Var,S<:Union{Var,Constant}}
    return Vector{APN}()
end

function sum_shift_neighbors(s::Sum; settings=default_settings())
    result = NeighborList()

    for i in content(get_bound(s))
        is_periodic(get_type(i)) || continue
        shifts = find_shift(i, get_body(s))
        unique!(shifts)
        for shift in shifts
            inv_shift = isa(shift, Add) ?
                        [mul(constant(-1), t) for t in content(get_body(shift))] :
                        [mul(constant(-1), shift)]
            new_body = simplify(subst(get_body(s), i, add(i, inv_shift...)); settings=settings) |> first
            push!(result, pct_sum(content(get_bound(s))..., new_body); name="shift")
        end
    end

    return result
end

"""
TODO: Allow the bound variables to pass through
sum(b, let t = ... end)
-> let t = ... sum(b, ...) end
"""
function bound_let_out(s::Sum)
    result = NeighborList()
    body = get_body(s)
    isa(get_body(s), Let) || return result
    interior, exterior = [], []
    for b in get_bound(s)
        free_let = union!(get_free(get_bound(body)), get_free(args(body)))
        if any(t -> get_body(t) == get_body(b), free_let)
            push!(exterior, b)
        else
            push!(interior, b)
        end
    end
    isempty(interior) && return result

    constructor = pct_sum
    new_term = pct_let(get_bound(body)..., args(body)...,
        constructor(interior..., get_body(body)))
    if !isempty(exterior)
        new_term = constructor(exterior..., new_term)
    end
    push!(result, new_term; dired=true, name="let_out_sum")
    return result
end

"""
sum((i, j), x(i) + y(j)) <-> sum((i, j), x(i)) + sum((i, j), y(j))
"""
function sum_dist_neighbors(s::Sum)
    result = NeighborList()
    a = get_body(s)
    isa(a, Add) || return result
    terms = content(get_body(a))
    push!(result, add([make_node(Sum, get_bound(s), t) for t in terms]...); dired=true, name="sum_dist")
    return result
end

function set_at(v::Any, i::Integer, h)
    map(j -> j == i ? h : v[j], 1:length(v))
end

function sub_neighbors(n::APN; settings=default_settings())
    result = NeighborList()
    sub_terms = terms(n)
    for (i, t) in enumerate(sub_terms)
        neighbor_list = neighbors(t, settings=settings)
        for (h, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            new_sub_terms = set_at(sub_terms, i, h)
            push!(result, set_terms(n, new_sub_terms...); dired=d, name=s)
            d && return result
        end

        any(directed(neighbor_list)) || tag_deadend!(t, settings)
    end
    return result
end

# function sum_delta_out(s::Sum)
#     result = NeighborList()
#     isa(get_body(s), Delta) || return result
#     delta = get_body(s)
#     any(t->contains_name(t, ff(s)), [upper(delta), lower(delta)]) && return result

#     return delta(upper(delta), lower(delta), pct_sum(ff(s)..., get_body(delta)))
# end

"""
sum(i, sum(j, ...)) -> sum((i,j), ...)
"""
function relax_sum(s::Sum)
    result = NeighborList()
    isa(get_body(s), Mul) || return result
    terms = content(get_body(get_body(s)))
    i = findfirst(t -> isa(t, Sum), terms)
    i === nothing && return result
    free = free_and_dummy(mul(terms[1:end.!=i]...)) |> first
    require_renaming(t) = name(t) in name.(free)
    symbols = new_symbol(terms..., num=count(require_renaming, content(get_bound(terms[i]))))
    new_ff = Vector{Var}()
    summand = get_body(terms[i])
    for t in content(get_bound(terms[i]))
        if require_renaming(t)
            new_var = var(pop!(symbols), get_type(t))
            push!(new_ff, new_var)
            summand = subst(summand, t, new_var)
        else
            push!(new_ff, t)
        end
    end

    push!(result, pct_sum(get_bound(s)..., new_ff..., mul(summand, terms[1:end.!=i]...)); dired=true, name="sum_in")
    return result
end

# TODO: Fix the bug of updating the type of the variable being absorbed!.
function sum_absorb_indicator(s::Sum)
    result = NeighborList()

    ind = get_body(s)
    isa(ind, Indicator) || return result
    indices = get_bound(s)

    function match_index(ind, indices, f)
        isa(f(ind), Var) || return nothing
        return findfirst(t -> name(t) == name(f(ind)), content(indices))
    end

    i_l = match_index(ind, indices, lower)
    i_u = match_index(ind, indices, upper)

    if i_l !== nothing
        curr_type = get_type(indices[i_l])
        curr_upper, curr_lower = upper(curr_type), lower(curr_type)
        if curr_upper == upper(ind) || curr_upper == upper(base(curr_type))
            new_domain = Domain(base(curr_type), curr_lower, upper(ind))
            new_index = set_type(indices[i_l], new_domain)
            new_body = subst(get_body(ind), indices[i_l], new_index)
            new_term = pct_sum(set_at(indices, i_l, new_index)..., new_body)
            push!(result, new_term; dired=true, name="absorb_upper_bound")
            return result
        end
    end
    if i_u !== nothing
        curr_type = get_type(indices[i_u])
        curr_upper, curr_lower = upper(curr_type), lower(curr_type)
        if curr_lower == lower(ind) || curr_lower == lower(base(curr_type))
            new_domain = Domain(base(curr_type), lower(ind), curr_upper)
            new_index = set_type(indices[i_u], new_domain)
            new_body = subst(get_body(ind), indices[i_u], new_index)
            new_term = pct_sum(set_at(indices, i_u, new_index)..., new_body)
            push!(result, new_term; dired=true, name="absorb_lower_bound")
            return result
        end
    end
    return result
end
basis_simplify(n::TerminalNode) = n

function basis_simplify(n::APN)
    simplified = combine_factors(n) |> nodes
    n = isempty(simplified) ? n : first(simplified)
end


function sum_eliminate_dead_bound(s::Sum)
    result = NeighborList()
    for b in get_bound(s)
        isa(get_type(b), ElementType) || continue
        u, l = upper(get_type(b)), lower(get_type(b))
        #= diff = simplify(subtract(u, l); settings=custom_settings(:expand_mul => true, :gcd => false, :logging => false)) |> first =#
        diff = basis_simplify(subtract(u, l))

        compare = zero_compare(diff)
        compare == IsNeg() || continue
        inner_type = get_type(get_body(s))
        new_inner = if isa(inner_type, ElementType)
            constant(0)
        elseif inner_type == FOT()
            fermi_scalar(constant(0))
        else
            error("sum of maps is not yet supported")
        end
        push!(result, new_inner; dired=true, name="dead_bound")
    end
    return result
end

# Extract Couple cluster intermediates
function extract_intermediate_neighbors(s::Sum)
    result = NeighborList()
    free, _ = free_and_dummy(s)
    free = filter(t -> isa(get_type(t), ElementType) && base(get_type(t)) == N(), free)
    if isempty(free)
        #= return result =#
        t = var(first(new_symbol(s; symbol=:_intm)), get_type(s))
        new_term = pct_let(pct_copy(t), s, t)
    else
        new_term = pct_map(free..., s)
        t = var(first(new_symbol(s; symbol=:_intm)), get_type(new_term))
        new_term = pct_let(pct_copy(t), new_term, call(t, free...))
    end
    push!(result, new_term; dired=true, name="extract_intermediate")
    return result
end

"""
(i::N{M}) -> ⋀ ((j::N{i}), f(j))

=> 

accumulate((i::N{M}), f(i))
"""
function iterator_to_accumuation(n::Map)

end


"""
(M::N{P}) ->
    ...
    (i::N{M}) -> ⋀ ((j::N{i}), f(j))

=>

(M::N{P}) -> 
    y = (i::N{P}) -> ⋀ ((j::N{i}), f(j))
    ...
    (i::N{M}) -> y(i)

=> 

y = (i::N{P}) -> ⋀ ((j::N{i}), f(j))
(M::N{P}) -> 
    ...
    (i::N{M}) -> y(i)
"""
function extract_iterator_intermediate(n::Map)

end


neighbor_registry[Sum] = [
]

function neighbors(s::Sum; settings=default_settings())

    result = NeighborList()
    time = @elapsed begin

        append!(result, contract_delta_neighbors(s))
        append!(result, sum_dist_neighbors(s))
        #= settings[:clench_sum] && append!(result, obvious_clench(s)) =#
        settings[:extract_intermediate] && !settings[:skip_self_as_intermediate] &&
            append!(result, extract_intermediate_neighbors(s))
        settings = custom_settings(:skip_self_as_intermediate => false; preset=settings)
        append!(result, obvious_clench(s))
        settings[:clench_sum] || append!(result, relax_sum(s))

        settings[:clench_sum] && append!(result, clench_sum(s))
        append!(result, sum_out_linear_op(s))
        append!(result, bound_let_out(s))
        append!(result, sum_out_delta(s))
        settings[:sum_absorb_indicator] && append!(result, sum_absorb_indicator(s))
        append!(result, sum_out_primitive_pullback(s))
        settings[:shift] && append!(result, sum_shift_neighbors(s; settings=settings))
        settings[:even_sym] && append!(result, sum_sym_neighbors(s))
        append!(result, sum_mul_neighbors(s))
        append!(result, sub_neighbors(s; settings=custom_settings(:gcd => false, :expand_mul => true; preset=settings)))
        append!(result, sum_eliminate_dead_bound(s))
        for edge in neighbor_registry[Sum]
            append!(result, edge(s))
        end
    end

    settings[:full_log] && println("exploring sum $(time)")
    return result
end

function prod_ex_neighbors(p::Prod)
    result = NeighborList()
    i, j = get_bound(p), get_bound(get_body(p))
    push!(result, pct_product(j, i, get_body(get_body(p))); name="prod_ex")
    return result
end

function prod_sym_neighbors(p::Prod)
    result = NeighborList()
    push!(result, set_content(p, subst(get_body(p), get_bound(p), mul(constant(-1), get_bound(p)))); name="prod_sym")
    return result
end

function prod_power_neighbors(p::Prod)
    result = NeighborList()
    d = get_type(get_bound(p))
    is_zero(get_body(p)) && return push!(result, constant(0); dired=true, name="prod_of_zeros")
    is_one(get_body(p)) && return push!(result, constant(1); dired=true, name="prod_of_ones")
    #TODO: Negative ones?
    range = add(upper(d), mul(constant(-1), lower(d)))
    push!(result, mul(get_body(p), range); dired=true, name="prod_power")
    return result
end

function prod_dist_neighbors(p::Prod)
    result = NeighborList()
    a = get_body(p)
    isa(get_body(p), Mul) || return result
    terms = content(get_body(a))
    for (i, t) in enumerate(terms)
        new_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, mul(pct_product(get_bound(p)..., t), pct_product(get_bound(p)..., add(new_terms...))); name="prod_dist")
    end
    return result
end

function prod_sum_neighbors(p::Prod)
    result = NeighborList()
    isa(get_body(p), Monomial) && !contains_name(base(get_body(p)), name(get_bound(p))) || return result
    push!(result, monomial(base(get_body(p)), pct_sum(get_bound(p), power(get_body(p)))); name="prod_sum")
    return result
end


function neighbors(p::Prod; settings=default_settings())
    result = NeighborList()

    append!(result, sub_neighbors(p; settings=settings))

    isa(get_body(p), Prod) && append!(result, prod_ex_neighbors(p))
    symmetric(get_bound(p)) && append!(result, prod_sym_neighbors(p))
    !contains_name(get_body(p), name(get_bound(p))) && append!(result, prod_power_neighbors(p))
    append!(result, prod_dist_neighbors(p))
    append!(result, prod_sum_neighbors(p))

    return result
end


function neighbors(d::Delta; settings=default_settings())
    result = NeighborList()
    
    append!(result, sub_neighbors(d; settings=settings))
    #= neighbor_list = neighbors(get_body(d); settings=settings)

    for (t, dir, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        push!(result, delta(upper(d), lower(d), t); dired=dir, name=s)
    end =#

    if isa(get_body(d), Delta)
        i, j = upper(d), lower(d)
        p, q = upper(get_body(d)), lower(get_body(d))
        # double-delta
        Set([i, j]) == Set([p, q]) &&
            base(get_type(i)) == N() &&
            base(get_type(j)) == N() &&
            push!(result, get_body(d); dired=true, name="double_delta")

        # Exchanging delta can be necessary
        #= settings[:delta_ex] && push!(result, delta(p, q, delta(i, j, get_body(get_body(d)))); name="delta_ex") =#
    end

    # TODO: use equivalence instead of equality
    upper(d) == lower(d) && push!(result, get_body(d); dired=true, name="delta_id")

    return result
end

function clench_delta(d::DeltaNot)
    result = NeighborList()
    isa(get_body(d), Mul) || return result

    f_u, d_u = free_and_dummy(upper(d))
    f_l, d_l = free_and_dummy(lower(d))
    isempty(d_u) && isempty(d_l) || return result

    function contain_script_var(n::APN)
        n_free = get_free(n)
        for f in union(f_u, f_l)
            name(f) in name.(n_free) && return true
        end
        return false
    end

    d_script = group(contain_script_var, content(get_body(get_body(d))))

    outer = get(d_script, false, [])
    isempty(outer) && return result
    inner = get(d_script, true, [])

    push!(result, mul(outer..., delta_not(upper(d), lower(d), mul(inner...))); dired=true, name="clench delta")

    return result
end

function neighbors(d::DeltaNot; settings=default_settings())
    result = NeighborList()
    append!(result, sub_neighbors(d; settings=settings))

    settings[:clench_delta] && append!(result, clench_delta(d))
    #= neighbor_list = neighbors(get_body(d); settings=settings)

    for (t, dir, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        push!(result, delta_not(upper(d), lower(d), t); dired=dir, name=s)
    end =#

    # TODO: use equivalence instead of equality
    upper(d) == lower(d) && push!(result, constant(0); dired=true, name="delta_not_id")

    return result
end


function dist_conj(c)
    result = NeighborList()
    isa(get_body(c), Add) || return result
    new_term = add(map(conjugate, content(get_body(get_body(c))))...)
    push!(result, new_term; dired=true, name="dist_conj")
    return result
end

function conj_comp(c)
    result = NeighborList()
    comp = get_body(c)
    isa(comp, Composition) || return result
    new_term = composite(map(conjugate, reverse(content(get_body(comp))))...)
    push!(result, new_term; dired=true, name="conj_comp")
    return result
end

function conj_scalar_op(c)
    result = NeighborList()
    scalar_op = get_body(c)
    isa(scalar_op, FermiScalar) || return result
    new_term = fermi_scalar(conjugate(get_body(scalar_op)))
    push!(result, new_term; dired=true, name="conj_scalar_op")
    return result
end

function neighbors(c::Conjugate; settings=default_settings())
    result = NeighborList()
    settings[:dist_conj] && append!(result, dist_conj(c))
    append!(result, conj_comp(c))
    append!(result, conj_scalar_op(c))
    append!(result, sub_neighbors(c; settings=settings))
    return result
end

function let_out_mul_add(n::T) where {T<:Union{Mul,Add}}
    result = let_out_vector(get_body(n))
    isempty(result) && return result

    new_let = first(first(result))
    new_let = pct_let(get_bound(new_let)..., args(new_let)...,
        make_node(T, get_body(new_let)))

    result = NeighborList()
    push!(result, new_let; dired=true, name="let_out_mul_add")
    return result
end

"""
(x, p, let p = q; f(p) end)

((a, b) -> let p = q
    (a, b, f(p))
end) (x, p)

let p' = q
    (x, p, f(p'))
end
"""
function let_out_vector(v::PCTVector)
    result = NeighborList()
    i = findfirst(t -> isa(t, Let), content(v))
    i === nothing && return result

    let_term = content(v)[i]
    new_vec = Vector{APN}(map(var, new_symbol(; num=length(v)), get_type.(content(v))))
    new_params = []
    new_args = []

    for j in 1:length(v)
        j == i && continue
        free = get_free(content(v)[j])
        if any(t -> name(t) in name.(free), get_bound(let_term))
            push!(new_params, new_vec[j])
            push!(new_args, content(v)[j])
        else
            new_vec[j] = content(v)[j]
        end
    end

    new_vec[i] = get_body(let_term)

    new_map = pct_map(new_params..., pct_let(get_bound(let_term)...,
        args(let_term)..., pct_vec(new_vec...)))

    @time push!(result, evaluate(call(new_map, new_args...)); dired=true, name="let_out_vector")
    return result
end

function neighbors(v::PCTVector; settings=default_settings())
    result = NeighborList()
    all(t -> isa(t, Var), content(v)) && return result
    append!(result, let_out_vector(v))
    append!(result, sub_neighbors(v; settings=settings))
    return result
end


function neighbors(v::Splat; settings=default_settings())

    result = NeighborList()
    if isa(get_body(v), Delta)
        d = get_body(v)
        push!(result, delta(upper(d), lower(d), splat(get_body(d))); dired=true, name="delta_out_splat")
    end
    append!(result, sub_neighbors(v; settings=settings))
    return result
end

function neighbors(v::Univariate; settings=default_settings())
    return sub_neighbors(v; settings=settings)
end

"""
x = delta(l, u, b)
y = x
x + y

-> 

x = b
y = delta(l, u, x)
delta(l, u, x)  + y

-> 
x = b
y = x
delta(l, u, x) + delta(l, u, y)
"""
function let_const_bound_delta_prop(lt::Let)
    result = NeighborList()
    bound = [get_bound(lt)...]
    new_args = [args(lt)...]
    body = get_body(lt)

    for i in 1:length(bound)
        v = new_args[i]
        if isa(v, Delta)
            u, l, b = upper(v), lower(v), get_body(v)
            new_args[i] = b
            d = delta(u, l, get_body(bound[i]))
        elseif isa(v, Map) && isa(get_body(v), Delta)
            inner_d = get_body(v)
            u, l, b = upper(inner_d), lower(inner_d), get_body(inner_d)
            new_args[i] = pct_map(get_bound(v)..., b)
            l_inputs = map(var, new_symbol(lt; num=length(get_type(get_bound(v)))), get_type(get_bound(v)))
            d = pct_map(l_inputs..., delta(u, l, call(get_body(bound[i]), l_inputs...)))
        else
            continue
        end
        new_let = pct_let(bound[1:i]..., new_args[1:i]...,
            eval_all(subst(pct_let(bound[i+1:end]..., new_args[i+1:end]..., body), get_body(bound[i]), d)))
        push!(result, new_let; dired=true, name="delta_prop")
        break
    end
    #= proped || return result
    push!(result, pct_let(bound..., new_args..., body); dired=true, name="delta_prop") =#
    return result
end

function let_const_body_delta_out(lt::Let)
    result = NeighborList()
    body = get_body(lt)
    isa(body, Delta) || return result
    u, l, b = upper(body), lower(body), get_body(body)

    any(t -> contains_name(pct_vec(u, l), name(t)),
        get_bound(lt)) && return result

    new_term = delta(u, l, pct_let(get_bound(lt)...,
        args(lt)..., b
    ))
    push!(result, new_term; dired=true, name="let_delta_out")
    return result
end

function let_collapse(lt::Let)
    result = NeighborList()
    inner_lt = get_body(lt)
    isa(inner_lt, Let) || return result
    n_b = length(get_bound(lt))
    n_b == length(get_bound(inner_lt)) || return result

    new_vars = map(var, new_symbol(lt; num=n_b), get_type.(get_bound(lt)))
    bounds = get_body.(get_bound(lt))
    inner_bounds = get_body.(get_bound(inner_lt))

    for i in 1:n_b
        new_arg = args(lt)[i]
        inner_new_arg = args(inner_lt)[i]
        for j in 1:i-1
            new_arg = subst(new_arg, bounds[j], new_vars[j])
            inner_new_arg = subst(inner_new_arg, inner_bounds[j], new_vars[j])
        end
        new_arg == inner_new_arg || return result
    end

    new_body = get_body(inner_lt)
    for i in 1:n_b
        new_body = subst(new_body, inner_bounds[i], bounds[i])
    end
    push!(result, pct_let(get_bound(lt)..., args(lt)..., new_body); dired=true, name="let_collapse")
    return result
end

# function let_collapse(lt::Let)
#     result = NeighborList()
#     inner_lt = get_body(lt)
#     isa(inner_lt, Let) || return result
#     get_bound(lt) == get_bound(inner_lt) || return result
#     args(lt) == args(inner_lt) || return result
#     push!(result, pct_let(get_bound(lt)..., args(lt)..., get_body(inner_lt)); dired=true, name="let_collapse")
#     return result
# end

function unused_let(lt::Let)
    result = NeighborList()
    for i in 1:length(get_bound(lt))
        free = get_free(pct_vec(args(lt)[i+1:end]..., get_body(lt)))
        name(get_bound(lt)[i]) in name.(free) && continue
        new_term = pct_let(get_bound(lt)[1:end.!=i]..., args(lt)[1:end.!=i]..., get_body(lt))
        push!(result, new_term; dired=true, name="unused_let")
        return result
    end
    return result
end

function sub_neighbors(lt::Let; settings=settings)

    result = NeighborList()
    lt_args = args(lt)
    p = sortperm(content(lt_args), by=t -> is_deadend(t, settings))

    for i = p
        # Base case of the intermediate extraction
        neighbor_list = neighbors(lt_args[i]; settings=custom_settings(:skip_self_as_intermediate => true, preset=settings))
        for (t, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content(lt, get_bound(lt), set_i(lt_args, i, t), get_body(lt)); dired=d, name=s)
            d && return result
        end
        any(directed(neighbor_list)) || tag_deadend!(lt_args[i], settings)
    end

    neighbor_list = neighbors(get_body(lt); settings=settings)
    for (t, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        push!(result, set_content(lt, get_bound(lt), lt_args, t); dired=d, name=s)
        d && return result
    end
    any(directed(neighbor_list)) || tag_deadend!(get_body(lt), settings)

    return result

end

function let_remove_alias(lt::Let; settings=default_settings())
    result = NeighborList()

    any(t -> isa(get_type(t), VecType), get_bound(lt)) || return result

    for i in 1:length(get_bound(lt))
        b = get_bound(lt)[i]
        a = args(lt)[i]
        isa(a, PCTVector) && all(t -> isa(t, Var), a[2:end]) || continue
        new_args = Vector{APN}(content(args(lt)[1:i-1]))
        push!(new_args, first(a))
        for j in i+1:length(get_bound(lt))
            new_b = subst(args(lt)[j], get_body(b), pct_vec(set_type(get_body(b), get_type(first(a))), a[2:end]...))
            push!(new_args, new_b)
        end

        new_body = subst(get_body(lt), get_body(b), pct_vec(set_type(get_body(b), get_type(first(a))), a[2:end]...))

        new_let = pct_let(get_bound(lt)..., new_args..., new_body)
        push!(result, eval_all(new_let); dired=true, name="remove_alias")
        break
    end
    return result
end

"""
Split assignment of a vector to a variable into 
a multi-assignment.

let b = (a_1, a_2)
 ...
end
->
let s_1, s_2 = (a_1, a_2)
 ...
end
"""
function let_split_multi_return(lt::Let, settings=default_settings())
    result = NeighborList()

    any(t -> isa(get_type(t), VecType), get_bound(lt)) || return result

    for i in 1:length(get_bound(lt))
        b = get_bound(lt)[i]
        a = args(lt)[i]
        isa(a, PCTVector) && !any(t -> isa(t, Var), a) || continue
        new_vars = pct_copy.(map(var, new_symbol(lt; num=length(a), symbol=:_s), get_content_type(get_type(a))))
        new_bound = Vector{APN}(content(get_bound(lt)[1:i-1]))
        new_args = Vector{APN}(content(args(lt)[1:i-1]))
        append!(new_args, content(a))
        append!(new_bound, new_vars)
        for j in i+1:length(get_bound(lt))
            new_b = subst(args(lt)[j], get_body(b), pct_vec(get_body.(new_vars)...))
            push!(new_bound, get_bound(lt)[j])
            push!(new_args, new_b)
        end

        new_body = subst(get_body(lt), get_body(b), pct_vec(get_body.(new_vars)...))
        new_let = pct_let(new_bound..., new_args..., new_body)
        push!(result, eval_all(new_let); dired=true, name="remove_multi_return")
        break
    end
    return result
end

need_pullback(v, node::APN) = any(t -> need_pullback(v, t), terms(node))
need_pullback(v, node::TerminalNode) = false
function need_pullback(v, node::PrimitivePullback)

    if isa(get_body(node), Map)
        m = get_body(node)
        body = get_body(m)
        isa(body, AbstractCall) || return false
        return name(mapp(body)) == name(v)
    end

    name(get_body(node)) == name(v) && return true
    invoke(need_pullback, Tuple{Any,APN}, v, node)
end

replace_pullback(n::APN, b, pb) = set_terms(n, map(t -> replace_pullback(t, b, pb), terms(n))...)
replace_pullback(n::TerminalNode, ::Any, ::Any) = n
function replace_pullback(n::PrimitivePullback, b, pb)
    """
    𝒫 (a -> h(a, b))(a, k)
    = 𝒫 (h)(a, b, k)(1)
    = ((a, k) -> 𝒫 (h)(a, b, k)(1))(a, k)
    """
    if isa(get_body(n), Map)
        m = get_body(n)
        bound, body = get_bound(m), get_body(m)
        length(bound) == 1 || error("multiple partial derivatives not yet supported")
        @assert isa(body, AbstractCall)
        name(mapp(body)) == name(b) || return invoke(replace_pullback, Tuple{APN,Any,Any}, n, b, pb)

        println(pretty(bound))
        println(pretty(body))
        i = findfirst(t -> t == first(bound), content(args(body)))
        @assert i !== nothing

        a_type = get_type(first(bound))
        k_type = get_type(body)
        a = var(first(new_symbol(n; symbol=Symbol("_$(name(first(bound)))"))), a_type)
        k = var(first(new_symbol(n, a; symbol=:_k)), k_type)

        result = pct_map(a, k, primitive_call(primitive_call(pb, set_i(args(body), i, a)..., k), constant(i)))
        return result

    end
    name(get_body(n)) == name(b) && return pb
    invoke(replace_pullback, Tuple{APN,Any,Any}, n, b, pb)
end


"""
mvp = ...
g = 𝒫(mvp)(...)

->

mvp = ...
pullback_mvp = ...

g = pullback_mvp(...)
"""

function link_pullback_neighbor(l::Let)
    result = NeighborList()
    new_bound = []
    new_args = []
    new_body = get_body(l)
    for i in 1:length(get_bound(l))
        b = get_bound(l)[i]
        a = args(l)[i]
        push!(new_args, a)
        push!(new_bound, b)
        any(t -> need_pullback(b, t), [args(l)[i+1:end]..., get_body(l)]) || continue

        pullback_name = first(new_symbol(get_bound(l)[i+1:end]..., args(l)[i+1:end]..., get_body(l); symbol=Symbol("_pullback_$(name(b))")))
        pullback_a = pullback(a)
        pullback_b = var(pullback_name, get_type(pullback_a))
        push!(new_args, pullback_a)
        push!(new_bound, pct_copy(pullback_b))
        for j in i+1:length(get_bound(l))
            d = get_bound(l)[j]
            c = args(l)[j]
            new_c = replace_pullback(c, b, pullback_b)
            push!(new_args, new_c)
            push!(new_bound, d)
        end
        new_body = replace_pullback(new_body, b, pullback_b)
        new_let = pct_let(new_bound..., new_args..., new_body)
        push!(result, new_let; dired=true, name="link_pullback")
        return result
    end
    return result
end


function neighbors(lt::Let; settings=default_settings())

    result = NeighborList()
    time = @elapsed begin
        append!(result, sub_neighbors(lt; settings=settings))
        append!(result, let_const_bound_delta_prop(lt))
        append!(result, let_const_body_delta_out(lt))
        append!(result, let_collapse(lt))
        append!(result, let_remove_alias(lt))
        append!(result, let_split_multi_return(lt))
        append!(result, cbi_to_mutation_neighbor(lt))
        # append!(result,unused_let(lt))
        settings[:link_pullback] && append!(result, link_pullback_neighbor(lt))
    end

    settings[:full_log] && println("exploring let $(time)")
    return result
end

"""
I(..., δ(...)) -> δ(..., I(...))
"""
function delta_swallow_indicator(ind)
    result = NeighborList()
    isa(get_body(ind), Delta) || return result
    d = get_body(ind)
    new_term = delta(lower(d), upper(d), indicator(upper(ind), lower(ind), get_body(d)))
    push!(result, new_term; name="delta_swallow_indicator", dired=true)
    return result
end

function neighbors(ind::Indicator; settings=default_settings())
    result = NeighborList()
    append!(result, delta_swallow_indicator(ind))
    settings[:dist_ind] && append!(result, dist_ind(ind))
    append!(result, sub_neighbors(ind; settings=settings))
    # append!(result, eliminate_indicator(ind))
    append!(result, telescopic_indicator_elim(ind))
    return result
end

"""
I(x,y, p + q) -> I(x, y, p) + I(x, y, q)
"""
function dist_ind(ind)
    result = NeighborList()
    a = get_body(ind)
    isa(a, Add) || return result
    new_term = add(map(t -> indicator(upper(ind), lower(ind), t), content(get_body(a)))...)
    push!(result, new_term; dired=true, name="dist_ind")
    return result
end

function telescopic_indicator_elim(ind; settings=default_settings())
    result = NeighborList()
    uppers, lowers = Vector{APN}([upper(ind)]), Vector{APN}([lower(ind)])
    body = get_body(ind)

    while isa(body, Indicator)
        push!(uppers, upper(body))
        push!(lowers, lower(body))
        body = get_body(body)
    end

    function remove_indicator!(j)
        uppers = uppers[1:end.!=j]
        lowers = lowers[1:end.!=j]
        for (l, u) in zip(lowers, uppers)
            body = indicator(u, l, body)
        end
        push!(result, body; dired=true, name="indicator_inclusion")
        return result
    end


    for (i, j) in Iterators.product(1:length(uppers), 1:length(uppers))
        i == j && continue
        u_i, l_i = uppers[i], lowers[i]
        u_j, l_j = uppers[j], lowers[j]

        u_i == u_j && l_i == l_j && return remove_indicator!(j)

        settings[:telescopic_indicator] || continue
        inclusion = subtract(subtract(u_j, l_j), subtract(u_i, l_i))

        exclusion = add(subtract(u_j, l_j), subtract(u_i, l_i))
        inclusion = simplify(inclusion; settings=custom_settings(:expand_mul => true, :logging => false; preset=default_settings())) |> first
        exclusion = simplify(exclusion; settings=custom_settings(:expand_mul => true, :logging => false; preset=default_settings())) |> first

        inclusion_test = zero_compare(inclusion)
        exclusion_test = zero_compare(exclusion)

        isa(inclusion_test, Union{IsZero,NonNeg,IsPos}) && return remove_indicator!(j)

        if isa(exclusion_test, IsNeg)
            push!(result, constant(0); dired=true, name="indicator_exclusion")
            return result
        end
    end
    return result
end


function eliminate_indicator(ind)
    result = NeighborList()
    diff = subtract(upper(ind), lower(ind))
    diff = simplify(diff; settings=custom_settings(:expand_mul => true, :gcd => false, :logging => false; preset=default_settings())) |> first
    compare_result = zero_compare(diff)

    if isa(compare_result, Union{IsPos,NonNeg,IsZero})
        push!(result, get_body(ind); dired=true, name="eliminate_indicator_satisfaction")
    elseif isa(compare_result, IsNeg)
        push!(result, constant(0); dired=true, name="eliminate_indicator_violation")
    end
    return result
end

function swallow_vac(v)
    result = NeighborList()
    T = typeof(get_body(v))
    T <: AbstractDelta || return result
    d = get_body(v)
    new_node = make_node(T, upper(d), lower(d), make_node(VacExp, get_body(d)))
    push!(result, new_node; name="swallow_vac", dired=true)
    return result
end

function extract_scalar(v)
    result = NeighborList()
    c = get_body(v)
    if isa(c, FermiScalar)
        push!(result, get_body(c); dired=true, name="extract_scalar")
        return result
    end

    isa(c, Composition) || return result
    terms = content(get_body(c))
    for (i, t) in enumerate(terms)
        isa(t, FermiScalar) || continue
        new_term = mul(get_body(t), vac_exp(composite(terms[1:end.!=i]...)))
        push!(result, new_term; dired=true, name="extract_scalar")
        return result
    end
    return result
end

function reduce_vac_early(v; settings=default_settings())
    result = NeighborList()
    c = get_body(v)
    isa(c, Composition) || return result

    terms = content(get_body(c))
    all(t -> is_creation(t) || is_annihilation(t), terms) || return result

    if settings[:wick]
        push!(result, wick_rewrite(get_body(v)); dired=true, name="wick_rewrite")
    else
        push!(result, reduce_vac(v); dired=true, name="reduce_vac_early")
    end

    return result
end

function neighbors(v::VacExp; settings=default_settings())
    result = NeighborList()

    settings[:reduce_vac_early] && append!(result, reduce_vac_early(v; settings))
    #= append!(result, extract_scalar(v)) =#
    append!(result, swallow_vac(v))
    append!(result, distribute_vac(v))
    append!(result, sub_neighbors(v; settings=custom_settings(:expand_comp => true, :dist_conj => true; preset=settings)))
    #= append!(result, mul_out_vac(v)) =#
    append!(result, sum_out_vac(v))
    return result
end


"""
⟨ a + b ⟩ = ⟨ a ⟩ + ⟨ b ⟩
"""
function distribute_vac(c)
    result = NeighborList()
    isa(get_body(c), Add) || return result
    term = get_body(c)
    push!(result, add(map(a -> make_node(VacExp, a), get_body(term))...); dired=true, name="distribute_vac")
    return result
end

#= function mul_out_vac(c)
    result = NeighborList()
    mul_term = get_body(c)
    isa(mul_term, Mul) || return result
    d = group(contains_field, content(get_body(mul_term)))

    new_term = mul(get(d, false, [])..., make_node(VacExp, mul(get(d, true, [])...)))
    push!(result, new_term; dired=true, name="mul out vac")
    return result
end =#

function sum_out_vac(c)
    result = NeighborList()
    term = get_body(c)
    isa(term, Sum) || return result
    new_term = pct_sum(get_bound(term)..., make_node(VacExp, get_body(term)))
    push!(result, new_term; dired=true, name="sum_out_vac")
    return result
end

#= function sum_out_comp(c)
    result = NeighborList()
    terms = content(get_body(c))
    i = findfirst(t->isa(t, Sum), terms)
    i === nothing && return result

    free = free_and_dummy(pct_vec(terms[1:end.!=i]...)) |> first
    require_renaming(t) = name(t) in name.(free)
    symbols = new_symbol(terms..., num=count(require_renaming, content(get_bound(terms[i]))))
    new_ff = Vector{Var}()
    summand = get_body(terms[i])

    for (i, t) in enumerate(terms)
        T = typeof(t)
        T <: Contraction || continue
        #= terms[i] = get_body(t) =#
        terms = set_i(terms, i, get_body(t))
        new_term = make_node(T, get_bound(t), composite(content(terms)...))
        push!(result, new_term; name="sum_out_comp", dired=true)
        return result
    end

    return result
end
 =#

function relax_sum_comp(c::Composition)
    result = NeighborList()
    terms = content(get_body(c))
    i = findfirst(t -> isa(t, Sum), terms)
    i === nothing && return result
    free = free_and_dummy(pct_vec(terms[1:end.!=i]...)) |> first
    require_renaming(t) = name(t) in name.(free)
    symbols = new_symbol(terms..., num=count(require_renaming, content(get_bound(terms[i]))))
    new_bound = Vector{Var}()
    summand = get_body(terms[i])
    for t in content(get_bound(terms[i]))
        if require_renaming(t)
            new_var = var(pop!(symbols), get_type(t))
            push!(new_bound, new_var)
            summand = subst(summand, t, new_var)
        else
            push!(new_bound, t)
        end
    end

    push!(result, pct_sum(new_bound..., composite(set_i(pct_vec(terms...), i, summand)...)); dired=true, name="relax_sum_comp")
    return result
end

function neighbors(c::Composition; settings=default_settings())
    result = NeighborList()
    settings[:clench_delta] || append!(result, swallow_neighbors(c))
    #= append!(result, sum_out_comp(c)) =#
    append!(result, relax_sum_comp(c))
    settings[:expand_comp] && append!(result, comp_expand_neighbors(c))
    append!(result, sub_neighbors(c; settings=settings))
    return result
end

function comp_expand_neighbors(c)
    result = NeighborList()

    terms = content(get_body(c))

    for i in 1:length(terms)
        left, right = terms[1:i-1], terms[i+1:end]
        t = terms[i]
        isa(t, Add) || continue
        new_term = add(map(a -> composite(left..., a, right...), get_body(t))...)
        push!(result, new_term; name="expand_comp", dired=true)
        break
    end
    return result
end

function mul_expand_const_neighbors(c)
    result = NeighborList()
    subterms = content(get_body(c))
    isa(first(subterms), Constant) || return result
    i = findfirst(t -> isa(t, Add), subterms)
    i === nothing && return result

    rest = subterms[1:end.!=i]

    new_add = add(map(t -> mul(first(subterms), t), content(get_body(subterms[i])))...)
    push!(result, mul(rest[2:end]..., new_add); name="expand_const", dired=true)
    return result
end

function mul_expand_neighbors(c)
    result = NeighborList()

    terms = content(get_body(c))

    for i in 1:length(terms)
        left, right = terms[1:i-1], terms[i+1:end]
        t = terms[i]
        isa(t, Add) || continue
        new_term = add(map(a -> mul(left..., a, right...), get_body(t))...)
        push!(result, new_term; name="expand_mul", dired=true)
        break
    end
    return result
end


function neighbors(n::APN; settings=default_settings())
    return sub_neighbors(n; settings=settings)
end

#= function let_const_bound_delta_prop(lt::Let)
    result = NeighborList()
    bound = [get_bound(lt)...]
    new_args = [args(lt)...]
    body = get_body(lt)

    proped = false
    for i in 1:length(bound)
        v = new_args[i]
        isa(v, Delta) || continue
        u, l, b = upper(v), lower(v), get_body(v)
        any(t -> if isa(t, Var) || isa(t, Copy)
                t in get_free(pct_vec(u, l))
            elseif isa(t, PCTVector)
                any(s -> s in get_free(pct_vec(u, l)), t)
            end, bound[1:i]) && continue
        new_args[i] = b
        for bd in v_wrap(bound[i])
            d = delta(u, l, get_body(bd))
            for j = i+1:length(bound)
                new_args[j] = subst(new_args[j], get_body(bd), d)
            end
            body = subst(body, get_body(bd), d)
        end
        proped = true
    end
    proped || return result
    push!(result, pct_let(bound..., new_args..., body); dired=true, name="delta_prop")
    return result
end =#

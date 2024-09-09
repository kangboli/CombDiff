using IterTools


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

function sub_neighbors(c::PrimitiveCall; settings=default_settings)
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

function delta_out_pullback_neighbors(c::PrimitiveCall)
    result = NeighborList()
    isa(mapp(c), AbstractPullback) || return result
    isa(get_body_type(get_type(get_body(mapp(c)))), VecType) && return result
    zs..., k = content(args(c))
    isa(k, Delta) || return result
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
function let_out_pullback(p::PrimitiveCall)
    result = NeighborList()
    isa(mapp(p), PrimitivePullback) || return result
    inner_map = get_body(mapp(p))
    map_output_type = get_body_type(get_type(inner_map))
    isa(map_output_type, VecType) && return result
    new_args..., let_term = content(args(p))
    isa(let_term, Let) || return result

    t = var(first(new_symbol(p)), MapType(VecType([get_type(let_term)]), get_type(p)))
    new_let = pct_map(t, pct_let(get_bound(let_term)..., args(let_term)...,
        call(t, get_body(let_term))))

    k = var(first(new_symbol(p, t)), get_type(let_term))
    new_map = pct_map(k, evaluate(call(mapp(p), new_args..., k)))

    push!(result, eval_all(call(new_let, new_map)); dired=true, name="let out pullback")
    return result
end

function neighbors(c::PrimitiveCall; settings=default_settings)
    result = NeighborList()

    append!(result, delta_out_pullback_neighbors(c))
    append!(result, let_out_pullback(c))
    function apply_symmetry(indices, op)
        # Apply the permutation.
        new_term = set_content(c, mapp(c), args(c)[collect(indices)])
        # Apply the symmetry operation.
        op == :conj && return conjugate(new_term)
        op == :id && return new_term
        op == :neg && return mul(constant(-1), new_term)
        if op == :ineg
            new_args = []
            for (i, a) in enumerate(content(args(c)))
                if i in indices
                    push!(new_args, mul(constant(-1), a))
                else
                    push!(new_args, a)
                end
            end
            return set_content(c, mapp(c), pct_vec(new_args...))
        end
        op == :inegc && error("Not yet properly implemented")
        #= return conjugate(set_content(c, mapp(c),
            [mul(constant(-1), t) for t in args(c)[collect(indices)]])) =#
        return new_term
    end

    append!(result, sub_neighbors(c; settings=settings))

    settings[:symmetry] || return result

    for (indices, op) in symmetries(get_type(mapp(c)))
        push!(result, apply_symmetry(indices, op); name="symmetry")
    end

    return result
end

function neighbors(::PrimitivePullback; settings=default_settings)
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

            is_one(common) && continue
            is_minus_one(common) && continue
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

function sub_neighbors(n::Union{Add,Mul}; settings=default_settings)
    result = NeighborList()
    body = get_body(n)
    for i = 1:length(body)
        neighbor_list = neighbors(body[i]; settings=settings)
        for (t, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content(n, set_i(body, i, t)); dired=d, name=s)
            d && return result
        end
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
    return add(remaining_terms..., new_maps...)
end

function combine_factors(a)
    result = NeighborList()
    terms = content(get_body(a))
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
    new_terms = [v == 1 ? k : mul(constant(v), k) for (k, v) in term_dict if v != 0]

    new_add = add(new_terms...)
    new_add == a && return result
    push!(result, add(new_terms...); dired=true, name="combine factors")

    return result
end


function neighbors(a::Add; settings=default_settings)
    result = NeighborList()
    terms = content(get_body(a))

    if count(a -> isa(a, Map), content(get_body(a))) > 1
        new_add = combine_maps(content(get_body(a)))
        push!(result, new_add; dired=true, name="combine map")
    end
    #= append!(result, combine_map_neighbors(terms)) =#
    append!(result, add_delta_neighbors(terms))
    sub_result = sub_neighbors(a; settings=settings)
    for (i, t) in enumerate(nodes(sub_result))
        isa(t, Add) && length(content(get_body(t))) == length(content(get_body(a))) && continue
        directed(sub_result)[i] = true
    end
    append!(result, sub_result)
    any(directed(result)) && return result

    settings[:gcd] && append!(result, gcd_neighbors(terms))
    append!(result, combine_factors(a))
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
            push!(result, mul(new_monomial, new_terms...); name="mul_add")
        end
    end
    return result
end

function swallow_neighbors(m::R) where {R<:Union{Mul,Composition}}
    result = NeighborList()
    terms = content(get_body(m))
    for (i, x) in enumerate(terms)
        T = typeof(x)
        T <: AbstractDelta || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, make_node(T, lower(x), upper(x), make_node(R, make_node(PCTVector, get_body(x), rem_terms...))); dired=true, name="swallow")
    end
    return result
end

function indicator_swallow_neighbors(terms)
    result = NeighborList()
    for (i, x) in enumerate(terms)
        isa(x, Indicator) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, indicator(lower(x), upper(x), mul(get_body(x), rem_terms...)); dired=true, name="indicator swallow mul")
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

function neighbors(m::Mul; settings=default_settings)
    result = NeighborList()
    terms = content(get_body(m))
    append!(result, mul_add_neighbors(terms))
    #= settings[:clench_sum] || append!(result, relax_sum(terms)) =#
    append!(result, swallow_neighbors(m))
    append!(result, indicator_swallow_neighbors(terms))
    settings[:expand_mul] && append!(result, mul_expand_neighbors(m))
    #= append!(result, mul_product_neighbors(terms)) =#
    #= append!(result, dist_neighbors(terms)) =#
    #= append!(result, prod_const_neighbors(terms)) =#
    append!(result, sub_neighbors(m; settings=settings))
    return result
end

function neighbors(m::Map; settings=default_settings)
    result = NeighborList()
    append!(result, sub_neighbors(m, settings=settings))
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



function neighbors(m::Monomial; _...)
    result = NeighborList()
    b, p = base(m), power(m)

    isa(p, Sum) && push!(result, pct_product(get_bound(p)..., monomial(b, get_body(p))); name="sum_prod")
    append!(result, add_mul_neighbors(m))
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
            push!(factors, add(upper(get_type(v)), mul(constant(-1), lower(get_type(v)))))
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

"""
sum(j, delta(i, j+k, A(i, j, k))) 
sets j -> i - k
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

        if isa(this, Var)
            replacement = other
        elseif isa(this, Add)
            replacement = add([mul(constant(-1), t) for t in content(get_body(this))]...)
            replacement = add(other, v, replacement)
        else
            #= mul(constant(-1), this) =#
            error("Not yet implemented")
        end
        new_sum = pct_sum(indices..., subst(get_body(d), v, replacement))
        new_sum = indicator(lower(get_type(this)), this, this, upper(get_type(this)), new_sum)

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
            push!(result, new_sum; dired=true, name="sum_clench")
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

function sum_out_linear_op(s::Sum)
    result = NeighborList()
    summand = get_body(s)
    (isa(summand, PrimitiveCall) ||
     (isa(summand, Conjugate) &&
      isa(get_body(summand), PrimitiveCall))) || return result
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

function sum_shift_neighbors(s::Sum)
    result = NeighborList()

    for i in content(get_bound(s))
        is_periodic(get_type(i)) || continue
        shifts = find_shift(i, get_body(s))
        unique!(shifts)
        for shift in shifts
            inv_shift = isa(shift, Add) ?
                        [mul(constant(-1), t) for t in content(get_body(shift))] :
                        [mul(constant(-1), shift)]
            push!(result, pct_sum(content(get_bound(s))..., subst(get_body(s), i, add(i, inv_shift...))); name="shift")
        end
    end

    return result
end

function sum_let_const_out(s::Sum)
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

    new_term = pct_sum(exterior...,
        pct_let(get_bound(body)..., args(body)...,
            pct_sum(interior..., get_body(body))))
    push!(result, new_term; dired=true, name="let out")
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

function sub_neighbors(n::APN; settings=default_settings)
    result = NeighborList()
    sub_terms = terms(n)
    for (i, t) in enumerate(sub_terms)
        neighbor_list = neighbors(t, settings=settings)
        for (h, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_terms(n, set_at(sub_terms, i, h)...); dired=d, name=s)
            d && return result
        end
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

function neighbors(s::Sum; settings=default_settings)
    result = NeighborList()

    append!(result, contract_delta_neighbors(s))
    append!(result, sum_dist_neighbors(s))
    #= settings[:clench_sum] && append!(result, obvious_clench(s)) =#
    append!(result, obvious_clench(s))
    append!(result, relax_sum(s))

    #= settings[:clench_sum] && append!(result, clench_sum(s)) =#
    append!(result, sum_out_linear_op(s))
    append!(result, sum_let_const_out(s))
    append!(result, sum_out_delta(s))
    if settings[:symmetry]
        append!(result, sum_shift_neighbors(s))
        append!(result, sum_sym_neighbors(s))
    end
    append!(result, sum_mul_neighbors(s))
    append!(result, sub_neighbors(s; settings=custom_settings(:gcd => false, :expand_mul => true; preset=settings)))
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


function neighbors(p::Prod; settings=default_settings)
    result = NeighborList()

    neighbor_list = neighbors(get_body(p), settings=settings)
    for (t, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        push!(result, set_content(p, t); dired=d, name=s)
    end

    isa(get_body(p), Prod) && append!(result, prod_ex_neighbors(p))
    symmetric(get_bound(p)) && append!(result, prod_sym_neighbors(p))
    !contains_name(get_body(p), name(get_bound(p))) && append!(result, prod_power_neighbors(p))
    append!(result, prod_dist_neighbors(p))
    append!(result, prod_sum_neighbors(p))

    return result
end


function neighbors(d::Delta; settings=default_settings)
    result = NeighborList()
    neighbor_list = neighbors(get_body(d); settings=settings)

    for (t, dir, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
        push!(result, delta(upper(d), lower(d), t); dired=dir, name=s)
    end

    if isa(get_body(d), Delta)
        i, j = upper(d), lower(d)
        p, q = upper(get_body(d)), lower(get_body(d))
        # double-delta
        Set([i, j]) == Set([p, q]) && push!(result, get_body(d); dired=true, name="double_delta")
        # delta-ex
        push!(result, delta(p, q, delta(i, j, get_body(get_body(d)))); name="delta_ex")
    end

    # TODO: use equivalence instead of equality
    upper(d) == lower(d) && push!(result, get_body(d); dired=true, name="delta_id")

    return result
end

function dist_conj(c)
    result = NeighborList()
    isa(get_body(c), Add) || return result
    new_term = add(map(conjugate, content(get_body(get_body(c))))...)
    push!(result, new_term; dired=true, name="dist conj")
    return result
end

function conj_comp(c)
    result = NeighborList()
    comp = get_body(c)
    isa(comp, Composition) || return result
    new_term = composite(map(conjugate, reverse(content(get_body(comp))))...)
    push!(result, new_term; dired=true, name="conj comp")
    return result
end

function conj_scalar_op(c)
    result = NeighborList()
    scalar_op = get_body(c)
    isa(scalar_op, FermiScalar) || return result
    new_term = fermi_scalar(conjugate(get_body(scalar_op)))
    push!(result, new_term; dired=true, name="conj scalar op")
    return result
end

function neighbors(c::Conjugate; settings=default_settings)
    result = NeighborList()
    settings[:dist_conj] && append!(result, dist_conj(c))
    append!(result, conj_comp(c))
    append!(result, conj_scalar_op(c))
    append!(result, sub_neighbors(c; settings=settings))
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
    new_vec[i] = get_body(let_term)

    new_map = pct_map(new_vec[1:end.!=i]..., pct_let(get_bound(let_term)...,
        args(let_term)..., pct_vec(new_vec...)))

    push!(result, evaluate(call(new_map, content(v)[1:end.!=i]...)); dired=true, name="let out vector")
    return result
end

function neighbors(v::PCTVector; settings=default_settings)
    result = NeighborList()
    all(t -> isa(t, Var), content(v)) && return result
    append!(result, let_out_vector(v))
    append!(result, sub_neighbors(v; settings=settings))
    return result
end


function neighbors(v::Univariate; settings=default_settings)
    return sub_neighbors(v; settings=settings)
end

function let_const_bound_delta_prop(lt::Let)
    result = NeighborList()
    bound = [get_bound(lt)...]
    new_args = [args(lt)...]
    body = get_body(lt)

    for i in 1:length(bound)
        v = new_args[i]
        isa(v, Delta) || continue
        u, l, b = upper(v), lower(v), get_body(v)
        any(t -> contains_name(pct_vec(u, l), name(t)), bound[1:i]) && continue
        new_args[i] = b
        d = delta(u, l, get_body(bound[i]))
        for j = i+1:length(bound)
            new_args[j] = subst(new_args[j], get_body(bound[i]), d)
        end
        body = subst(body, get_body(bound[i]), d)
    end
    push!(result, pct_let(bound..., new_args..., body); dired=true, name="delta prop")
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
    push!(result, new_term; dired=true, name="let delta out")
    return result
end

function let_collapse(lt::Let)
    result = NeighborList()
    inner_lt = get_body(lt)
    isa(inner_lt, Let) || return result
    get_bound(lt) == get_bound(inner_lt) || return result
    args(lt) == args(inner_lt) || return result
    push!(result, pct_let(get_bound(lt)..., args(lt)..., get_body(inner_lt)); dired=true, name="let collapse")
    return result
end

function neighbors(lt::Let; settings=default_settings)
    result = NeighborList()
    append!(result, sub_neighbors(lt; settings=settings))
    append!(result, let_const_bound_delta_prop(lt))
    append!(result, let_const_body_delta_out(lt))
    append!(result, let_collapse(lt))
    return result
end

function delta_swallow_indicator(ind)
    result = NeighborList()
    isa(get_body(ind), Delta) || return result
    d = get_body(ind)
    new_term = delta(lower(d), upper(d), indicator(lower(ind), upper(ind), get_body(d)))
    push!(result, new_term; name="delta_swallow_indicator", dired=true)
    return result
end

function neighbors(ind::Indicator; settings=default_settings)
    result = NeighborList()
    append!(result, delta_swallow_indicator(ind))
    settings[:dist_ind] && append!(result, dist_ind(ind))
    append!(result, sub_neighbors(ind; settings=settings))
    #= append!(result, eliminate_indicator(ind)) =#
    append!(result, telescopic_indicator_elim(ind))
    return result
end

function dist_ind(ind)
    result = NeighborList()
    isa(get_body(ind), Add) || return result
    new_term = add(map(t -> indicator(lower(ind), upper(ind), t), content(get_body(get_body(ind))))...)
    push!(result, new_term; dired=true, name="dist_ind")
    return result
end

function telescopic_indicator_elim(ind; settings=default_settings)
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
            body = indicator(l, u, body)
        end
        push!(result, body; dired=true, name="indicator inclusion")
        return result
    end


    for (i, j) in product(1:length(uppers), 1:length(uppers))
        i == j && continue
        u_i, l_i = uppers[i], lowers[i]
        u_j, l_j = uppers[j], lowers[j]

        u_i == u_j && l_i == l_j && return remove_indicator!(j)

        settings[:telescopic_indicator] || continue
        inclusion = subtract(subtract(u_j, l_j), subtract(u_i, l_i))

        exclusion = add(subtract(u_j, l_j), subtract(u_i, l_i))
        inclusion = simplify(inclusion; settings=custom_settings(:expand_mul => true, :logging => false; preset=default_settings)) |> first
        exclusion = simplify(exclusion; settings=custom_settings(:expand_mul => true, :logging => false; preset=default_settings)) |> first

        inclusion_test = zero_compare(inclusion)
        exclusion_test = zero_compare(exclusion)

        isa(inclusion_test, Union{IsZero,NonNeg,IsPos}) && return remove_indicator!(j)

        if isa(exclusion_test, IsNeg)
            push!(result, constant(0); dired=true, name="indicator exclusion")
            return result
        end
    end
    return result
end


function eliminate_indicator(ind)
    result = NeighborList()
    diff = add(upper(ind), mul(constant(-1), lower(ind)))
    diff = simplify(diff; settings=custom_settings(:expand_mul => true, :logging => false; preset=default_settings)) |> first
    compare_result = zero_compare(diff)

    isa(compare_result, Union{IsPos,NonNeg}) || return result
    push!(result, get_body(ind); dired=true, name="eliminate_indicator")
    return result
end

function swallow_vac(v)
    result = NeighborList()
    T = typeof(get_body(v))
    T <: AbstractDelta || return result
    d = get_body(v)
    new_node = make_node(T, lower(d), upper(d), make_node(VacExp, get_body(d)))
    push!(result, new_node; name="swallow vac", dired=true)
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

function reduce_vac_early(v)
    result = NeighborList()
    c = get_body(v)
    isa(c, Composition) || return result

    terms = content(get_body(c))
    all(is_field_op, terms) || return result

    push!(result, reduce_vac(v); dired=true, name="reduce_vac_early")

    return result
end

function neighbors(v::VacExp; settings=default_settings)
    result = NeighborList()

    settings[:reduce_vac_early] && append!(result, reduce_vac_early(v))
    append!(result, extract_scalar(v))
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
    push!(result, add(map(a -> make_node(VacExp, a), get_body(term))...); dired=true, name="distribute vac")
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
    push!(result, new_term; dired=true, name="sum out vac")
    return result
end

function neighbors(c::Composition; settings=default_settings)
    result = NeighborList()
    settings[:expand_comp] && append!(result, comp_expand_neighbors(c))
    append!(result, swallow_neighbors(c))
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
        push!(result, new_term; name="expand comp", dired=true)
        break
    end
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
        push!(result, new_term; name="expand mul", dired=true)
        break
    end
    return result
end


function neighbors(n::FermiScalar; settings=default_settings)
    return sub_neighbors(n; settings=settings)
end


export neighbors, NeighborList, directed, nodes

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

neighbors(_::Union{Var,Constant}) = NeighborList()

function sub_neighbors(c::PrimitiveCall)
    result = NeighborList()
    a = args(c)

    for i in 1:length(a)
        neighbor_list = neighbors(a[i])
        for (t, d, n) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content(c, mapp(c), set_i(a, i, t)); dired=d, name=n)
        end
    end

    return result
end

function neighbors(c::PrimitiveCall)
    result = NeighborList()

    append!(result, sub_neighbors(c))
    return result
end

#= function apply_symmetry(indices, op)
    new_term = set_content(c, mapp(c), args(c)[collect(indices)])
    op == :conj && return conjugate(new_term)
    op == :neg && return mul(constant(-1), new_term)
    return new_term
end

for (indices, op) in symmetries(get_type(mapp(c)))
    push!(result, apply_symmetry(indices, op), name="symmetry")
end =#


"""
Currently, we do not extract powers. For example, `i^2 + i` will be not  
factored into `i*(i+1)`.
"""
function gcd(a::APN, b::APN)
    a_rem = Vector{APN}()
    b_rem = Vector{APN}(isa(b, Mul) ? content(fc(b)) : [b]) # New copy
    c = Vector{APN}()

    for t in (isa(a, Mul) ? content(fc(a)) : [a])
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

    node_from_set(s) = length(s) > 1 ? mul(s...) : first(collect(s))
    return map(node_from_set, (a_rem, b_rem, c))
end


function gcd_neighbors(terms::Vector)
    result = NeighborList()
    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            x_rem, y_rem, common = gcd(x, y)

            is_one(common) && continue
            push!(result, add(mul(common, add(x_rem, y_rem)),
                    terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]...); name="gcd")
        end
    end
    return result
end


"""
sum((i::I1, j::I2), x(i, j)) + sum((p::I1, q::I3), y(p, q)) <-> 
sum((i::I1), sum(j::I2, x(i, j)) + sum(q::I3, y(i, q)))
"""
function add_sum_neighbors(terms::Vector)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Sum) && isa(y, Sum) || continue

            common_x, common_y = Vector{Var}(), Vector{Var}()

            y_rem = Vector{APN}(content(ff(y)))

            for v in content(ff(x))
                for (i, u) in enumerate(y_rem)
                    get_type(v) == get_type(u) || continue
                    push!(common_x, v)
                    push!(common_y, u)
                    deleteat!(y_rem, i)
                    break
                end
            end

            isempty(common_x) && continue

            x_rem = filter(t -> !(t in common_x), content(ff(x)))
            y_rem = filter(t -> !(t in common_y), content(ff(y)))

            new_names = new_symbol(x, y, num=length(common_x))
            new_vars = Vector{Var}([var(s, d) for (s, d) in zip(new_names, get_type.(common_x))])

            new_x = renaming(common_x, new_vars, fc(x))
            isempty(x_rem) || (new_x = pct_sum(x_rem..., new_x))

            new_y = renaming(common_y, new_vars, fc(y))
            isempty(x_rem) || (new_y = pct_sum(y_rem..., new_y))

            new_sum = pct_sum(new_vars..., add(new_x, new_y))
            new_terms = terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]

            push!(result, add(new_sum, new_terms...); name="add_sum")
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

function sub_neighbors(n::Union{Add,Mul})
    result = NeighborList()
    c = fc(n)
    for i = 1:length(c)
        neighbor_list = neighbors(c[i])
        for (t, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content(n, set_i(c, i, t)); dired=d, name=s)
        end
    end

    return result
end

function add_const_neighbors(terms)
    result = NeighborList()
    constants = filter(t -> isa(t, Constant), terms)
    nonconstants = filter(t -> !isa(t, Constant), terms)
    length(constants) > 1 || return result

    new_const = make_node(Constant, sum(fc, constants))
    push!(result, add(new_const, nonconstants...); dired=true, name="add_const")
    return result
end


function neighbors(a::Add)
    result = NeighborList()
    terms = content(fc(a))
    append!(result, sub_neighbors(a))
    append!(result, gcd_neighbors(terms))
    append!(result, add_sum_neighbors(terms))
    append!(result, add_delta_neighbors(terms))
    append!(result, add_const_neighbors(terms))

    return result
end

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

function swallow_neighbors(terms)
    result = NeighborList()
    for (i, x) in enumerate(terms)
        isa(x, Delta) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, delta(lower(x), upper(x), mul(fc(x), rem_terms...)); dired=true, name="swallow")
    end
    return result
end

function mul_product_neighbors(terms)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Prod) && isa(y, Prod) && get_type(ff(x)) == get_type(ff(y)) || continue
            z = make_node(Var, first(new_symbol(x, y)); type=get_type(ff(x)))
            new_prod = make_node(Prod, z, mul(subst(fc(x), ff(x), z), subst(fc(y), ff(y), z)))
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
        push!(result, add(content(map(n -> mul(rem_terms..., n), fc(t)))...); name="dist")
    end
    return result
end

function prod_in_neighbors(terms)
    result = NeighborList()
    for (i, t) in enumerate(terms)
        isa(t, Sum) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]

        if contains_name(rem_terms..., name(ff(t)))
            t = set_from(t, first(new_symbol(rem_terms..., t)))
        end

        push!(result, set_content(t, mul(fc(t), rem_terms)); name="prod_in")
    end
    return result
end

function prod_const_neighbors(terms)
    result = NeighborList()
    constants = filter(t -> isa(t, Constant), terms)
    nonconstants = filter(t -> !isa(t, Constant), terms)
    length(constants) > 1 || return result

    new_const = make_node(Constant, prod(fc, constants))
    new_term = is_one(new_const) ? mul(nonconstants...) :
               mul(new_const, nonconstants...)
    push!(result, new_term; dired=true, name="prod_const")
    return result
end


function neighbors(m::Mul)
    result = NeighborList()
    terms = content(fc(m))
    #= length(terms) == 1 && push!(result, first(terms); dired=true, name="mul_collapse") =#

    append!(result, sub_neighbors(m))
    append!(result, mul_add_neighbors(terms))
    #= any(is_zero, terms) && push!(result, make_node(Constant, 0); dired=true, name="mul_zero") =#
    append!(result, swallow_neighbors(terms))
    append!(result, mul_product_neighbors(terms))
    append!(result, dist_neighbors(terms))
    append!(result, prod_const_neighbors(terms))

    return result
end

function add_mul_neighbors(m::Monomial)
    result = NeighborList()
    b, p = base(m), power(m)
    isa(p, Add) || return result
    terms = content(fc(p))
    for (i, t) in enumerate(terms)
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, mul(monomial(b, t), monomial(b, add(rem_terms...))); name="add_mul")
    end
    return result
end



function neighbors(m::Monomial)
    result = NeighborList()
    b, p = base(m), power(m)

    # Sum mul neighbors
    isa(p, Sum) && push!(result, pct_product(ff(p), monomial(b, fc(p))); name="sum_prod")
    #= is_zero(b) && push!(result, make_node(Constant, 0); dired=true, name="power_of_zero")
    !is_zero(b) && is_zero(p) && push!(result, make_node(Constant, 1); dired=true, name="zeroth_power") =#
    append!(result, add_mul_neighbors(m))
    return result
end

#= function sum_ex_neighbors(s::Sum)
    result = NeighborList()
    i, j = ff(s), ff(fc(s))
    push!(result, pct_sum(j, pct_sum(i, fc(fc(s)))); name="sum_ex")
    return result
end =#

function sum_sym_neighbors(s::Sum)
    result = NeighborList()

    for v in content(ff(s))
        symmetric(get_type(v)) || continue
        push!(result, set_content(s, subst(fc(s), v, mul(constant(-1), v))); name="sum_sym")
    end

    return result
end

"""
sum(i, k) = N ⋅ k
"""
function sum_mul_neighbors(s::Sum)
    result = NeighborList()

    i_rem = Vector{APN}()
    factors = Vector{APN}()

    for v in content(ff(s))
        if isa(get_type(v), Domain)
            push!(factors, add(upper(v), mul(constant(-1), lower(v))))
        else
            push!(i_rem, v)
        end
    end

    isempty(factors) && return result

    if isempty(i_rem)
        push!(result, mul(factors..., fc(s)); dired=true, name="sum_mul")
    else
        push!(result, mul(factors..., pct_sum(i_rem..., fc(s))); dired=true, name="sum_mul")
    end

    #= is_zero(fc(s)) && push!(result, constant(0); dired=true, name="sum_of_zero") =#
    #= push!(result, mul(range, fc(s)); dired=true, name="sum_mul") =#
    return result
end

function contract_delta_neighbors(s::Sum)
    result = NeighborList()
    d = fc(s)
    isa(d, Delta) || return result

    for (i, v) in enumerate(content(ff(s)))
        indices = content(remove_i(ff(s), i))
        if v == upper(d)
            new_sum = pct_sum(indices..., subst(fc(d), v, lower(d)))
            push!(result, new_sum; dired=true, name="contract_delta")
        elseif v == lower(d)
            new_sum = pct_sum(indices..., subst(fc(d), v, upper(d)))
            push!(result, new_sum; dired=true, name="contract_delta")
        end
    end

    return result
end

"""
sum(i, j, k ⋅ x(i) ⋅ y(j)) -> k ⋅ sum(i, x(i) ⋅ sum(j, y(j)))
"""
function sum_out_neighbors(s::Sum)
    result = NeighborList()

    mul_term = fc(s)
    isa(mul_term, Mul) || return result

    for (i, v) in enumerate(content(ff(s)))
        interior, exterior = Vector{APN}(), Vector{APN}()

        for t in content(fc(mul_term))
            target = contains_name(t, name(v)) ? interior : exterior
            push!(target)
        end

        isempty(exterior) && continue
        new_v = remove_i(ff(s), i)
        new_sum = pct_sum(new_v, mul(exterior..., pct_sum(ff(s)[i], mul(interior))))
        push!(result, new_sum; dired=true, name="sum_out")
    end

    return result
end

"""
sum(i, sum(j, x(i, j))) -> sum((i, j), x(i, j))
"""
function sum_merge_neighbors(s::Sum)
    result = NeighborList()
    isa(fc(s), Sum) || return result

    new_indices = pct_vec(vcat(content(ff(s)), content(ff(fc(s))))...)
    push!(result, pct_sum(new_indices, fc(fc(s))); dired=true, name="sum_merge")

    return result
end


"""
sum((i, j), x(i) + y(j)) <-> sum((i, j), x(i)) + sum((i, j), y(j))
"""
function sum_dist_neighbors(s::Sum)
    result = NeighborList()
    a = fc(s)
    isa(a, Add) || return result
    terms = content(fc(a))
    for (i, t) in enumerate(terms)
        new_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, add(make_node(Sum, ff(s), t), make_node(Sum, ff(s), add(new_terms...))); name="sum_dist")
    end
    return result
end

function set_at(v::Any, i::Integer, h)
    map(j -> j == i ? h : v[j], 1:length(v))
end

function sub_neighbors(n::APN)
    result = NeighborList()
    sub_terms = terms(n)
    for (i, t) in enumerate(sub_terms)
        neighbor_list = neighbors(t)
        for (h, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_terms(n, set_at(sub_terms, i, h)...); dired=d, name=s)
        end
    end
    return result
end

function neighbors(s::Sum)
    result = NeighborList()

    append!(result, sub_neighbors(s))
    append!(result, sum_out_neighbors(s))
    append!(result, sum_dist_neighbors(s))
    append!(result, contract_delta_neighbors(s))
    append!(result, sum_sym_neighbors(s))
    append!(result, sum_mul_neighbors(s))
    #= isa(fc(s), Sum) && append!(result, sum_ex_neighbors(s)) =#

    return result
end

function prod_ex_neighbors(p::Prod)
    result = NeighborList()
    i, j = ff(p), ff(fc(p))
    push!(result, pct_product(j, pct_product(i, fc(fc(p)))); name="prod_ex")
    return result
end

function prod_sym_neighbors(p::Prod)
    result = NeighborList()
    push!(result, set_content(p, subst(fc(p), ff(p), mul(constant(-1), ff(p)))); name="prod_sym")
    return result
end

function prod_power_neighbors(p::Prod)
    result = NeighborList()
    d = get_type(ff(p))
    is_zero(fc(p)) && return push!(result, constant(0); dired=true, name="prod_of_zeros")
    is_one(fc(p)) && return push!(result, constant(1); dired=true, name="prod_of_ones")
    #TODO: Negative ones?
    range = add(upper(d), mul(constant(-1), lower(d)))
    push!(result, mul(fc(p), range); dired=true, name="prod_power")
    return result
end

function prod_dist_neighbors(p::Prod)
    result = NeighborList()
    a = fc(p)
    isa(fc(p), Mul) || return result
    terms = content(fc(a))
    for (i, t) in enumerate(terms)
        new_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, mul(pct_product(ff(p), t), pct_product(ff(p), add(new_terms...))); name="prod_dist")
    end
    return result
end

function prod_sum_neighbors(p::Prod)
    result = NeighborList()
    isa(fc(p), Monomial) && !contains_name(base(fc(p)), name(ff(p))) || return result
    push!(result, monomial(base(fc(p)), pct_sum(ff(p), power(fc(p)))); name="prod_sum")
    return result
end


function neighbors(p::Prod)
    result = NeighborList()

    neighbor_list = neighbors(fc(p))
    for (t, s) in zip(nodes(neighbor_list), names(neighbor_list))
        push!(result, set_content(p, t); name=s)
    end

    isa(fc(p), Prod) && append!(result, prod_ex_neighbors(p))
    symmetric(get_type(ff(p))) && append!(result, prod_sym_neighbors(p))
    !contains_name(fc(p), name(ff(p))) && append!(result, prod_power_neighbors(p))
    append!(result, prod_dist_neighbors(p))
    append!(result, prod_sum_neighbors(p))

    return result
end


function neighbors(d::Delta)
    result = NeighborList()
    neighbor_list = neighbors(fc(d))
    for (t, s) in zip(nodes(neighbor_list), names(neighbor_list))
        push!(result, delta(upper(d), lower(d), t); name=s)
    end

    if isa(fc(d), Delta)
        i, j = upper(d), lower(d)
        p, q = upper(fc(d)), lower(fc(d))
        # delta-ex
        push!(result, delta(p, q, delta(i, j, fc(fc(d)))); name="delta_ex")
        # double-delta
        Set([i, j]) == Set([p, q]) && push!(result, fc(d); dired=true, name="double_delta")
    end

    # TODO: use equivalence instead of equality
    upper(d) == lower(d) && push!(result, fc(d); dired=true, name="delta_id")

    return result
end

function neighbors(c::Conjugate)
    result = NeighborList()
    append!(result, sub_neighbors(c))
    return result
end

function neighbors(v::PCTVector)
    all(t -> isa(t, Var), content(v)) && return NeighborList()
    return sub_neighbors(v)
end



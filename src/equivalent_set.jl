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
Base.iterate(n::NeighborList, state::Integer) = state > length(n) ? nothing : (n[state], state+1)

function Base.getindex(n::NeighborList, i::Integer)
    return (nodes(n)[i], directed(n)[i])
end

function Base.append!(n_1::NeighborList, n_2::NeighborList)
    append!(n_1.nodes, n_2.nodes)
    append!(n_1.directed, n_2.directed)
    append!(n_1.names, n_2.names)
    return n_1
end

function pretty(n::NeighborList)
    join(map((name, t)->"$(name): $(pretty(t))", names(n), nodes(n)), "\n")
end

function Base.show(io::IO, ::MIME"text/plain", n::NeighborList)
    print(io, pretty(n))
end

neighbors(_::Union{Var, Constant}) = NeighborList()

function neighbors(c::PrimitiveCall)
    result = NeighborList()
    a = args(c)

    for i = 1:length(a)
        neighbor_list = neighbors(a[i])
        map((n, d) -> push!(result, set_content!(c, mapp(c), set_i(a, i, n)), d), 
            nodes(neighbor_list), directed(neighbor_list))
    end

    function apply_symmetry(indices, op)
        new_term = set_content!(c, mapp(c), args(c)[collect(indices)])
        op == :conj && return make_node!(Conjugate, new_term)
        return new_term
    end

    for (indices, op) in symmetries(get_type(mapp(c)))
        push!(result, apply_symmetry(indices, op), name="symmetry")
    end
    return result
end

function gcd(a::APN, b::APN)
    a_set = Set(isa(a, Mul) ? content(fc(a)) : [a])
    b_set = Set(isa(b, Mul) ? content(fc(b)) : [b])

    c = intersect(a_set, b_set)

    a_rem = setdiff(a_set, c)
    b_rem = setdiff(b_set, c)

    fill_one(x) = isempty(x) ? Set([make_node!(Constant, 1)]) : x

    a_rem, b_rem, c = map(fill_one, (a_rem, b_rem, c))

    node_from_set(s) = length(s) > 1 ? mul(s...) : first(collect(s))
    return map(node_from_set, (a_rem, b_rem, c))
end

is_zero(t) = isa(t, Constant) && fc(t) == 0
is_one(t) = isa(t, Constant) && fc(t) == 1

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


function add_sum_neighbors(terms::Vector)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Sum) && isa(y, Sum) && get_type(ff(x)) == get_type(ff(y)) || continue
            
            z = make_node!(Var, first(new_symbol(x, y)); type=get_type(ff(x)))
            new_sum = make_node!(Sum, z, add(subst(fc(x), ff(x), z), subst(fc(y), ff(y), z)))

            push!(result, add(new_sum, terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]...);name="add_sum")

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
            push!(result, add(new_delta, terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]...); dired=true, name="add_delta")
        end
    end
    return result
end

function sub_neighbors(n::Union{Add, Mul})
    result = NeighborList()
    c = fc(n)
    for i = 1:length(c)
        neighbor_list = neighbors(c[i])
        for (t, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content!(n, set_i(c, i, t)); dired=d, name=s)
        end
    end

    return result
end

function add_const_neighbors(terms)
    result = NeighborList()
    constants = filter(t->isa(t, Constant), terms) 
    nonconstants = filter(t->!isa(t, Constant), terms) 
    length(constants) > 1 || return result

    new_const = make_node!(Constant, sum(fc, constants))
    push!(result, add(new_const, nonconstants...); dired=true, name="add_const")
    return result
end


function neighbors(a::Add)
    result = NeighborList()
    terms = content(fc(a))
    length(terms) == 1 && push!(result, first(terms); dired=true, name="add_collapse")
    append!(result, sub_neighbors(a))
    append!(result, gcd_neighbors(terms))
    # add-to-zero edge
    any(is_zero, terms) && push!(result, add(collect(filter(t -> !is_zero(t), terms))...); dired=true, name="add_to_zero")
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
            
            new_monomial = make_node!(Monomial, base(x), add(power(x), power(y)))
            push!(result, mul(new_monomial, terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]...); name="mul_add")
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
            z = make_node!(Var, first(new_symbol(x, y)); type=get_type(ff(x)))
            new_sum = make_node!(Prod, z, add(subst(fc(x), ff(x), z), subst(fc(y), ff(y), z)))
            push!(result, add(new_sum, terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]...);name="mul_product")
        end
    end
    return result
end

function dist_neighbors(terms::Vector)
    result = NeighborList()
    for (i, t) in enumerate(terms)
        isa(t, Add) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, add(content(map(n->mul(rem_terms..., n), fc(t)))...); name="dist")
    end
    return result
end

function prod_in_neighbors(terms)
    result = NeighborList()
    for (i, t) in enumerate(terms)
        isa(t, Sum) || continue
        rem_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]

        if contains_name(rem_terms..., name(ff(t))) 
            t = set_from!(t, first(new_symbol(rem_terms..., t)))
        end

        push!(result, set_content!(t, mul(fc(t), rem_terms)); name="prod_in")
    end
    return result
end

function prod_const_neighbors(terms)
    result = NeighborList()
    constants = filter(t->isa(t, Constant), terms) 
    nonconstants = filter(t->!isa(t, Constant), terms) 
    length(constants) > 1 || return result

    new_const = make_node!(Constant, prod(fc, constants))
    new_term = is_one(new_const) ? mul(nonconstants...) :
                                mul(new_const, nonconstants...)
    push!(result, new_term; dired=true, name="prod_const")
    return result
end


function neighbors(m::Mul)
    result = NeighborList()
    terms = content(fc(m))
    length(terms) == 1 && push!(result, first(terms); dired=true, name="mul_collapse")

    append!(result, sub_neighbors(m))
    append!(result, mul_add_neighbors(terms))
    any(is_zero, terms) && push!(result, make_node!(Constant, 0); dired=true, name="mul_zero")
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
        push!(result, mul(make_node!(Monomial, b, t), make_node!(Monomial, b, add(rem_terms...))); name="add_mul")
    end
    return result
end



function neighbors(m::Monomial)
    result = NeighborList()
    b, p = base(m), power(m)
    isa(b, Constant) && isa(p, Constant) && push!(result, make_node!(Constant, fc(b)^fc(p)); name="monomial_const")
    is_one(p) && push!(result, b; dired=true, name="unit_power")
    append!(result, [make_node!(Monomial, t, p) for t in neighbors(b)])
    append!(result, [make_node!(Monomial, b, t) for t in neighbors(p)])

    # Sum mul neighbors
    isa(p, Sum) && push!(result, make_node!(Prod, ff(p), make_node!(Monomial, b, fc(p))); name="sum_mul")

    is_zero(b) && push!(result, make_node!(Constant, 0); dired=true, name="power_of_zero")
    !is_zero(b) && is_zero(p) && push!(result, make_node!(Constant, 1); dired=true, name="zeroth_power")
    append!(result, add_mul_neighbors(m))
    return result
end

function sum_ex_neighbors(s::Sum)
    result = NeighborList()
    i, j = ff(s), ff(fc(s))
    push!(result, make_node!(Sum, j, make_node!(Sum, i, fc(fc(s)))); name="sum_ex")
    return result
end

function sum_sym_neighbors(s::Sum)
    result = NeighborList()
    push!(result, set_content!(s, subst(fc(s), ff(s), mul(make_node!(Constant, -1), ff(s)))); name="sum_sym")
    return result
end

function sum_mul_neighbors(s::Sum)
    result = NeighborList()
    d = get_type(ff(s))
    is_zero(fc(s)) && push!(result, make_node!(Constant, 0); dired=true, name="sum_of_zero")
    range = add(upper(d), mul(make_node!(Constant, -1), lower(d)))
    push!(result, mul(range, fc(s)); dired=true, name="sum_mul")
    return result
end

function contract_delta_neighbors(s::Sum)
    result = NeighborList()
    d = fc(s)
    isa(d, Delta) || return result
    if ff(s) == upper(d)
        push!(result, subst(fc(d), ff(s), lower(d)); dired=true, name="contract_delta")
    elseif ff(s) == lower(d)
        push!(result, subst(fc(d), ff(s), upper(d)); dired=true, name="contract_delta")
    end
    return result
end

function sum_out_neighbors(s::Sum)
    result = NeighborList()

    mul_term = fc(s)
    isa(mul_term, Mul) || return result


    interior = filter(t->contains_name(t, name(ff(s))), content(fc(mul_term)))
    exterior = filter(t->!contains_name(t, name(ff(s))), content(fc(mul_term)))
    
    if !isempty(exterior)
        push!(result, mul(exterior..., make_node!(Sum, ff(s), mul(interior...))); name="sum_out")
    end
    
    return result
end

function sum_dist_neighbors(s::Sum)
    result = NeighborList()
    a = fc(s)
    isa(a, Add) || return result
    terms = content(fc(a))
    for (i, t) in enumerate(terms)
        new_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, add(make_node!(Sum, ff(s), t), make_node!(Sum, ff(s), add(new_terms...))); name="sum_dist")
    end
    return result
end

function set_at(v::Any, i::Integer, h)
    map(j->j==i ? h : v[j], 1:length(v))
end


function sub_neighbors(n::APN)
    result = NeighborList()
    sub_terms = terms(n)
    for (i, t) in enumerate(sub_terms)
        neighbor_list = neighbors(t)
        for (h, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_terms!(n, set_at(sub_terms, i, h)...); dired=d, name=s)
        end
    end
    return result
end

function neighbors(s::Sum)
    result = NeighborList()

    append!(result, sub_neighbors(s))
    isa(fc(s), Sum) && append!(result, sum_ex_neighbors(s))
    symmetric(get_type(ff(s))) && append!(result, sum_sym_neighbors(s))
    !contains_name(fc(s), name(ff(s))) && append!(result, sum_mul_neighbors(s))

    isa(fc(s), Delta) && ff(s) in [upper(fc(s)), lower(fc(s))] && 
    append!(result, contract_delta_neighbors(s))

    append!(result, sum_dist_neighbors(s))
    append!(result, sum_out_neighbors(s))

    return result
end

function prod_ex_neighbors(p::Prod)
    result = NeighborList()
    i, j = from(p), from(fc(p))
    push!(result, make_node!(Prod, j, make_node!(Prod, i, fc(fc(p)))); name="prod_ex")
    return result
end

function prod_sym_neighbors(p::Prod)
    result = NeighborList()
    push!(result, set_content!(p, subst(fc(p), ff(p), mul(make_node!(Constant, -1), ff(p)))); name="prod_sym")
    return result
end

function prod_power_neighbors(p::Prod)
    result = NeighborList()
    d = get_type(ff(p))
    is_zero(fc(p)) && return push!(result, make_node!(Constant, 0); dired=true, name="prod_of_zeros")
    is_one(fc(p)) && return push!(result, make_node!(Constant, 1); dired=true, name="prod_of_ones")
    #TODO: Negative ones?
    range = add(d.upper, mul(make_node!(Constant, -1), d.lower))
    push!(result, make_node!(Monomial, fc(p), range); dired=true, name="prod_power")
    return result
end

function prod_dist_neighbors(p::Prod)
    result = NeighborList()
    a = fc(p)
    isa(fc(p), Mul) || return result
    terms = fc(a)
    for (i, t) in enumerate(terms)
        new_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, mul(make_node!(Prod, ff(p), t), make_node!(Prod, ff(p), add(new_terms...))); name="prod_dist")
    end
    return result
end

function prod_sum_neighbors(p::Prod)
    result = NeighborList()
    isa(fc(p), Monomial) && !contains_name( base(fc(p)), name(ff(p))) || return result
    push!(result, make_node!(Monomial, base(fc(p)), make_node!(Sum, ff(p), power(fc(p)))); name="prod_sum")
    return result
end


function neighbors(p::Prod)
    result = NeighborList()

    neighbor_list = neighbors(fc(p))
    for (t, s) in zip(nodes(neighbor_list), names(neighbor_list))
        push!(result, set_content!(p, t); name=s)
    end

    isa(fc(p), Prod) && append!(result, prod_ex_neighbors(p))
    symmetric(get_type(ff(p))) && append!(result, prod_sym_neighbors(p))
    !contains_name(fc(p), ff(p)) && append!(result, prod_power_neighbors(p))
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
        push!(result, delta( p, q, delta(i, j, fc(fc(d)))); name="delta_ex")
        # double-delta
        Set([i, j]) == Set([p, q]) && push!(result, fc(d); dired=true, name="double_delta")
    end

    # TODO: use equivalence instead of equality
    upper(d) == lower(d) && push!(result, fc(d); dired=true, name="delta_id")

    return result
end


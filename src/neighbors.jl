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
Combine the addition of two sums into one. Exchange of summation indices is not allowed.

sum((i::I1, j::I2), x(i, j)) + sum((p::I1, q::I3), y(p, q)) <-> 
sum((i::I1), sum(j::I2, x(i, j)) + sum(q::I3, y(i, q)))
"""
function add_sum_neighbors(terms::Vector)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Sum) && isa(y, Sum) || continue

            max_length = min(length(ff(x)), length(ff(y)))
            k_max = findfirst(k->get_type(ff(x)[k]) != get_type(ff(y)[k]), 1:max_length)
            k_max == 1 && continue
            k_max === nothing && (k_max = max_length)
            x_rem = content(ff(x))[k_max+1:end]
            y_rem = content(ff(y))[k_max+1:end]
            new_names = new_symbol(x, y; num=k_max)
            new_vars = pct_vec(map(k->var(new_names[k], get_type(ff(x)[k])), 1:k_max)...)
            new_x = subst(fc(x), ff(x)[1:k_max], new_vars)
            new_y = subst(fc(y), ff(y)[1:k_max], new_vars)
            #= println("x:")
            println(pretty.(content(ff(x)[1:k_max])), "->", pretty.(content(new_vars)))
            println(pretty(fc(x)))
            println(pretty(new_x))
            println("y:")
            println(pretty.(content(ff(y)[1:k_max])), "->", pretty.(content(new_vars)))
            println(pretty(fc(y)))
            println(pretty(new_y)) =#
            isempty(x_rem) || (new_x = pct_sum(x_rem..., new_x))
            isempty(y_rem) || (new_y = pct_sum(y_rem..., new_y))

            new_sum = pct_sum(content(new_vars)..., add(new_x, new_y))
            #= println("new_sum: ", pretty(new_sum)) =#
            new_terms = terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]
            push!(result, add(new_sum, new_terms...); dired=true, name="add_sum")
        end
    end
    return result
end

#= for (n, v) in enumerate(content(ff(x)))
    for (m, u) in enumerate(content(ff(y)))
        get_type(v) == get_type(u) || continue
        y_rem = remove_i(ff(y), m)
        x_rem = remove_i(ff(x), n)
        new_name = first(new_symbol(x, y))
        new_var = var(new_name, get_type(v))
        new_x = subst(fc(x), v, new_var)
        new_y = subst(fc(y), u, new_var)
        isempty(content(x_rem)) || (new_x = pct_sum(content(x_rem)..., new_x))
        isempty(content(x_rem)) || (new_y = pct_sum(content(y_rem)..., new_y))
        new_sum = pct_sum(new_var, add(new_x, new_y))
        new_terms = terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]
        push!(result, add(new_sum, new_terms...); name="add_sum")
    end
end =#

"""
delta((i, k), (j, l), A(i,j,k,l))  + delta((m, k), (n, l), A(m,n,k,l))
-> delta(k, l, delta(i, j, A(i,j,k,l)) + delta(m, n, A(m,n,k,l)))
"""
function add_delta_neighbors(terms::Vector)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Delta) && isa(y, Delta) || continue

            x_rem = Vector{Tuple{APN, APN}}()
            y_rem = collect(zip(content(upper(y)), content(lower(y))))
            common = Vector{Tuple{APN, APN}}()

            for (ux, lx) in zip(content(upper(x)), content(lower(x)))
                for (i, (uy, ly)) in enumerate(y_rem)
                    if Set([ux, lx]) == Set([uy, ly])
                        push!(common, (ux, lx))
                        deleteat!(y_rem, i)
                    else
                        push!(x_rem, (ux, lx))
                    end
                end
            end

            isempty(common) && continue

            x_inner = fc(x)
            isempty(x_rem) || (x_inner = delta(pct_vec(first.(x_rem)...), pct_vec(last.(x_rem)...), fc(x)))

            y_inner = fc(y)
            isempty(y_rem) || (y_inner = delta(pct_vec(first.(y_rem)...), pct_vec(last.(y_rem)...), fc(y)))

            new_delta = delta(pct_vec(first.(common)...), pct_vec(last.(common)...), add(x_inner, y_inner))
            
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

"""
∏((i,j), A(i,j)) * ∏((p, j), B(p,j)) = ∏(j, ∏(i, A(i, j)) * ∏(p, B(p, j)))
"""
function mul_product_neighbors(terms)
    result = NeighborList()

    for (i, x) in enumerate(terms)
        for (j, y) in enumerate(terms)
            i < j || continue
            isa(x, Prod) && isa(y, Prod) || continue
            for (r, v) in enumerate(content(ff(x)))
                s = findfirst(t->get_type(t) == get_type(v), content(ff(y))) 
                s===nothing && continue
                y_remain = remove_i(ff(y), s)
                x_remain = remove_i(ff(x), r)
                z = var(first(new_symbol(x, y)), get_type(v))
                new_x = pct_product(content(x_remain)..., fc(x))
                new_y = pct_product(content(y_remain)..., fc(y))
                new_prod = pct_product(z, mul(subst(new_x, v, z), subst(new_y, v, z)))
                new_terms = terms[collect(filter(k -> k != i && k != j, 1:length(terms)))]
                push!(result, mul(new_prod, new_terms...); name="mul_product")
            end
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
    isa(p, Sum) && push!(result, pct_product(content(ff(p))..., monomial(b, fc(p))); name="sum_prod")
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
            push!(factors, add(upper(get_type(v)), mul(constant(-1), lower(get_type(v)))))
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
        for (j, (u, l)) in enumerate(zip(content(upper(d)), content(lower(d))))
            #= println("v: ", typeof(v),", l: ", typeof(l),", u: ", typeof(u)) =#
            #= println("v==l: ", v==l, ", v==u: ", v==u)
            println("name(v)==name(l): ", name(v)==name(l)) =#
            if v == u
                new_upper = subst(remove_i(upper(d), j), v, l)
                new_lower = subst(remove_i(lower(d), j), v, l)
                new_sum = pct_sum(indices..., delta(new_upper, new_lower, subst(fc(d), v, l)))
                #= println("---------------------------------")
                println("v: ", pretty(v))
                println("u: ", pretty(u))
                println("new indices: ", pretty.(indices))
                println("old: ", pretty(s))
                println("new: ", pretty(new_sum)) =#
                #= length(indices) < 4 && println("ERROR in Contraction!") =#
                push!(result, new_sum; dired=true, name="contract_delta")
            elseif v == l
                new_upper = subst(remove_i(upper(d), j), v, u)
                new_lower = subst(remove_i(lower(d), j), v, u)
                new_sum = pct_sum(indices..., delta(new_upper, new_lower, subst(fc(d), v, u)))
                push!(result, new_sum; dired=true, name="contract_delta")
            end
        end
    end

    return result
end

"""
Move factors that are independent of the summation indices out of the sum.
Exchange of the summation indices are not allowed.
    
sum(i, j, k ⋅ x(i) ⋅ y(j)) -> k ⋅ sum(i, x(i) ⋅ sum(j, y(j)))
"""
function sum_out_neighbors(s::Sum)
    result = NeighborList()
    mul_term = fc(s)
    isa(mul_term, Mul) || return result
    inner_index = last(content(ff(s)))
    outer_indices = remove_i(ff(s), length(ff(s)))
    interior, exterior = Vector{APN}(), Vector{APN}()
    for t in content(fc(mul_term))
        target = contains_name(t, name(inner_index)) ? interior : exterior
        push!(target, t)
    end
    isempty(exterior) && return result
    new_sum = pct_sum(content(outer_indices)..., mul(exterior..., pct_sum(inner_index, mul(interior...))))
    push!(result, new_sum; dired=false, name="sum_out")
    return result
end

"""
sum(i, sum(j, x(i, j))) -> sum((i, j), x(i, j))
"""
function sum_merge_neighbors(s::Sum)
    result = NeighborList()
    isa(fc(s), Sum) || return result
    new_indices = pct_vec(vcat(content(ff(s)), content(ff(fc(s))))...)
    push!(result, pct_sum(content(new_indices)..., fc(fc(s))); dired=true, name="sum_merge")
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
        push!(result, add(pct_sum(content(ff(s))..., t), 
             pct_sum(content(ff(s))..., add(new_terms...))); name="sum_dist")
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
    #= append!(result, sum_out_neighbors(s)) =#
    append!(result, sum_merge_neighbors(s))
    append!(result, sum_dist_neighbors(s))
    append!(result, contract_delta_neighbors(s))
    append!(result, sum_sym_neighbors(s))
    append!(result, sum_mul_neighbors(s))
    #= isa(fc(s), Sum) && append!(result, sum_ex_neighbors(s)) =#
    return result
end

#= function prod_ex_neighbors(p::Prod)
    result = NeighborList()
    i, j = ff(p), ff(fc(p))
    push!(result, pct_product(j, pct_product(i, fc(fc(p)))); name="prod_ex")
    return result
end =#

function prod_sym_neighbors(p::Prod)
    result = NeighborList()

    for v in content(ff(p))
        symmetric(get_type(v)) || continue
        push!(result, set_content(p, subst(fc(p), v, mul(constant(-1), v))); name="prod_sym")
    end

    return result
end

function prod_power_neighbors(p::Prod)
    result = NeighborList()

    vars = free_variables(fc(p))
    for v in content(ff(p))
        v in vars && continue
        d = get_type(v)
        #TODO: Negative ones?
        range = add(upper(d), mul(constant(-1), lower(d)))
        push!(result, mul(fc(p), range); dired=true, name="prod_power")
    end
    return result
end

function prod_dist_neighbors(p::Prod)
    result = NeighborList()
    a = fc(p)
    isa(fc(p), Mul) || return result
    terms = content(fc(a))
    for (i, t) in enumerate(terms)
        new_terms = terms[collect(filter(k -> k != i, 1:length(terms)))]
        push!(result, mul(pct_product(content(ff(p))..., t), pct_product(content(ff(p))..., add(new_terms...))); name="prod_dist")
    end
    return result
end

function prod_sum_neighbors(p::Prod)
    result = NeighborList()
    inner = filter(v->!contains_name(base(fc(p)), name(v)), content(ff(p)))
    outer = filter(v->contains_name(base(fc(p)), name(v)), content(ff(p)))
    isempty(inner) && return result
    #= isa(fc(p), Monomial) && !contains_name(base(fc(p)), name(ff(p))) || return result =#
    new_power = pct_sum(inner..., power(fc(p)))
    push!(result, pct_product(outer..., monomial(base(fc(p)), new_power)); name="prod_sum")
    return result
end


function neighbors(p::Prod)
    result = NeighborList()

    neighbor_list = neighbors(fc(p))
    for (t, s) in zip(nodes(neighbor_list), names(neighbor_list))
        push!(result, set_content(p, t); name=s)
    end

    is_zero(fc(p)) && return push!(result, constant(0); dired=true, name="prod_of_zeros")
    is_one(fc(p)) && return push!(result, constant(1); dired=true, name="prod_of_ones")
    #= isa(fc(p), Prod) && append!(result, prod_ex_neighbors(p)) =#
    append!(result, prod_sym_neighbors(p))
    append!(result, prod_power_neighbors(p))
    append!(result, prod_dist_neighbors(p))
    append!(result, prod_sum_neighbors(p))

    return result
end


function neighbors(d::Delta)
    result = NeighborList()
    append!(result, sub_neighbors(d))
    append!(result, delta_merge_neighbors(d))
    return result
end

function delta_merge_neighbors(d::Delta)
    result = NeighborList()
    isa(fc(d), Delta) || return result
    
    new_upper = append!(upper(d), upper(fc(d)))
    new_lower = append!(lower(d), lower(fc(d)))
    push!(result, delta(new_upper, new_lower, fc(fc(d))); dired=true, name="delta_merge")
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


    #= for (i, v) in enumerate(content(ff(s)))
        interior, exterior = Vector{APN}(), Vector{APN}()

        for t in content(fc(mul_term))
            target = contains_name(t, name(v)) ? interior : exterior
            push!(target, t)
        end

        isempty(exterior) && continue
        new_v = remove_i(ff(s), i)
        new_sum = pct_sum(content(new_v)..., mul(exterior..., pct_sum(ff(s)[i], mul(interior...))))
        push!(result, new_sum; dired=true, name="sum_out")
    end 

    return result =#

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

function add_const_neighbors(terms)
    result = NeighborList()
    constants = filter(t -> isa(t, Constant), terms)
    nonconstants = filter(t -> !isa(t, Constant), terms)
    length(constants) > 1 || return result

    new_const = make_node(Constant, sum(fc, constants))
    push!(result, add(new_const, nonconstants...); dired=true, name="add_const")
    return result
end


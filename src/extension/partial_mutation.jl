
struct PartialMutation <: APN
    type::AbstractPCTType
    target::APN
    value::APN
end

get_target(m::PartialMutation) = m.target
get_value(m::PartialMutation) = m.value
get_body(m::PartialMutation) = get_body(get_value(m))

content_fields(::Type{PartialMutation}) = [:target, :value]

function subst(m::PartialMutation, v::Var, new::APN, b::Bool)
    name(get_target(m)) == name(v) && error("substitution of a mutation target is not allowed")
    invoke(subst, Tuple{PartialMutation,APN,APN,Bool}, m, v, new, b)
end

function partial_mutation(target::APN, value::APN)
    make_node(PartialMutation, target, value)
end

function partial_inference(::Type{PartialMutation}, target::APN, _)
    return get_type(target)
end

function cbi_to_mutation(m::CBI, b::APN)
    update = simplify(pct_map(get_bound(m)..., subtract(get_body(m), call(b, get_bound(m)...)))) |> first

    body = get_body(update)
    ts, us, ls = collect_delta(body)

    absorb_indices = []
    for b in get_bound(m)
        i = findfirst(t -> t == b, us)
        i = i === nothing ? findfirst(t -> t == b, ls) : i
        push!(absorb_indices, i === nothing ? 0 : i)
    end

    function absorb(j::Int)
        z = get_bound(m)[j]
        i = absorb_indices[j]
        i > 0 || return z
        ts[i] == Delta || error("absorbing $(ts[i]) is not yet supported")
        us[i] == z && return set_type(z, parametrize_type(N(), ls[i], ls[i]))
        ls[i] == z && return set_type(z, parametrize_type(N(), us[i], us[i]))
    end

    absorbed_bounds = map(absorb, 1:length(absorb_indices))

    remaining_indices = filter(i -> !(i in absorb_indices), 1:length(ts))

    new_body = foldr(((t, u, l), b) -> make_node(t, u, l, b),
        zip(ts[remaining_indices], us[remaining_indices], ls[remaining_indices]); init=get_body_delta(body))

    values = pct_map(absorbed_bounds..., new_body)

    return partial_mutation(b, values)
end

function pretty(m::PartialMutation)
    value = get_value(m)
    bound_strs = []
    for b in get_bound(value)
        if lower(get_type(b)) == upper(get_type(b))
            push!(bound_strs, pretty(lower(get_type(b))))
        else
            push!(bound_strs, "$(pretty(lower(get_type(b)))):$(pretty(upper(get_type(b))))")
        end
    end
    return "$(pretty(get_target(m)))($(join(bound_strs, ","))) <| $(pretty(get_body(get_value(m))))"
end

function collect_delta(d::T) where {T<:AbstractDelta}
    body = get_body(d)
    isa(body, AbstractDelta) || return [T], [v_wrap(upper(d))...], [v_wrap(lower(d))...]
    T_rest, upper_rest, lower_rest = collect_delta(body)
    return [T, T_rest...], [v_wrap(upper(d))..., upper_rest...], [v_wrap(lower(d))..., lower_rest...]
end

get_body_delta(n::APN) = n

get_body_delta(d::AbstractDelta) = get_body_delta(get_body(d))

"""
For the purpose of immediate inplace operations, the write location 
must symbolically agree with the read location.
"""
function validate_write_location(n::APN, v::Var, bounds::PCTVector)
    name(v) in name.([get_free(n)...]) || return true
    all(t -> validate_write_location(t, v, bounds), terms(n))
end

validate_write_location(::TerminalNode, ::Var, ::PCTVector) = true

function validate_write_location(n::PrimitiveCall, v::Var, bounds::PCTVector)
    if isa(mapp(n), Var) && name(mapp(n)) == name(v)
        return args(n) == bounds
    end
    return invoke(validate_write_location, Tuple{APN,Var,PCTVector}, n, v, bounds)
end


function validate_mem_size(n::APN, b)
    free = [get_free(n)...]
    i = findfirst(t -> name(t) == name(b), free)
    i === nothing && return false
    return get_type(free[i]) == get_type(b)
end

function cbi_to_mutation_neighbor(l::Let)
    result = NeighborList()

    new_args = []
    modifed = false
    for (b, a) in zip(get_bound(l), args(l))
        if !(validate_mem_size(a, b) && isa(a, CBI) && validate_write_location(get_body(a), get_body(b), get_bound(a)))
            push!(new_args, a)
            continue
        end
        push!(new_args, cbi_to_mutation(a, get_body(b)))
        modifed = true
    end

    modifed || return result
    mutated = pct_let(get_bound(l)..., new_args..., get_body(l))
    push!(result, mutated; dired=true, name="mutation")
    return result
end


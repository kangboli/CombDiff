using Accessors
export reverse_inference

reverse_inference(n::TerminalNode) = n

function reverse_inference(n::APN)
    set_terms(n, map(reverse_inference, terms(n))...)
end

function reverse_inference(m::Map)
    new_bounds = []
    new_body = reverse_inference(get_body(m))
    for b in get_bound(m)
        if is_undetermined_type(get_type(b))
            b_types = retrieve_type_from_usage(b, new_body)
            if !isempty(b_types)
                push!(new_bounds, set_type(b, first(b_types)))
            else
                push!(new_bounds, b)
            end
        else
            push!(new_bounds, b)
        end
    end
    return pct_map(new_bounds..., new_body)
end

function reverse_inference(c::T) where {T<:AbstractCall}
    new_args = []
    c_mapp = mapp(c)
    if !is_undetermined_type(get_type(c_mapp))
        for (a, t) in zip(args(c), get_bound_type(get_type(c_mapp)))
            if is_undetermined_type(get_type(a))
                push!(new_args, set_type(a, t))
            else
                push!(new_args, a)
            end
        end
        #= println.(verbose.(new_args)) =#
    elseif isa(c_mapp, Constructor) && !is_undetermined_type(get_type(c))
        for (a, t) in zip(args(c), get_content_type(get_type(c)))
            if is_undetermined_type(get_type(a))
                push!(new_args, set_type(a, t))
            else
                push!(new_args, a)
            end
        end
        c_mapp = set_type(c_mapp, MapType(VecType(get_type.(new_args)), get_type(c)))
    elseif !is_undetermined_type(get_type(c)) && !is_undetermined_type(get_type(args(c)))
        new_args = args(c)
        if isa(get_type(c_mapp), MapType)
            c_mapp = set_type(c_mapp, MapType(VecType(get_type.(new_args)), get_type(c)))
        elseif isa(get_type(c_mapp), AbstractVecType)
            new_type = set_i(get_type(c_mapp), get_body(first(new_args)), get_type(c))
            c_mapp = set_type(c_mapp, new_type)
        end
    end

    #= return make_node(T, c_mapp, pct_vec(map(reverse_inference, new_args)...)) =#
    new_call = make_node(T, c_mapp, pct_vec(new_args...))
    #= new_call = make_node(T, c_mapp, pct_vec(map(reverse_inference, new_args)...)) =#
    result = invoke(reverse_inference, Tuple{APN}, new_call)
    #= println("====")
    println(verbose(c))
    println(verbose(c_mapp))
    println(verbose(new_call))
    println(verbose(result))
    println("====") =#
    return result
end

function retrieve_type_from_usage(r::Var, s::Var)
    return name(r) == name(s) ? [get_type(s)] : []
end

retrieve_type_from_usage(::Var, ::TerminalNode) = []

function retrieve_type_from_usage(v::Var, body::APN)
    free = get_free(body)
    name(v) in name.(free) || return []
    result = vcat(map(t -> retrieve_type_from_usage(v, t), terms(body))...)
    return [reduce(merge_type, result; init=UndeterminedPCTType())]
    #= return result =#
end

merge_type(::UndeterminedPCTType, t::AbstractPCTType) = t
merge_type(s::AbstractPCTType, ::UndeterminedPCTType) = s
merge_type(::UndeterminedPCTType, ::UndeterminedPCTType) = UndeterminedPCTType()

function merge_type(::S, ::T) where {S<:AbstractPCTType,T<:AbstractPCTType}
    error("reverse inference failed. $(S) and $(T) cannot be matched")
end

function merge_type(s::T, t::T) where {T<:AbstractDomain}
    lower(s) == lower(t) && upper(s) == upper(t) || error("reverse inference failed. $(pretty(s)) and $(pretty(t)) cannot be matched")
end

function merge_type(s::T, t::T) where {T<:AbstractVecType}
    length(s) == length(t) || error("reverse inference failed. $(pretty(s)) and $(pretty(t)) cannot be matched")
    merged_content = map(merge_type, get_content_type(s), get_content_type(t))
    return @set s.content = merged_content
end

function merge_type(s::T, t::T) where {T<:AbstractMapType}
    merged_bound = map(merge_type, zip(get_bound_type(s), get_bound_type(t)))
    merged_body = merge_type(get_body_type(s), get_body_type(t))
    return @set (@set s.bound = merged_bound).body = merged_body
end


#= function retrieve_type_from_usage(v::APN, body::AbstractCall)

    for (a, t) in zip(args(body), get_bound_type(get_type(mapp(body))))
        if isa(a, Var)
            (name(v) == name(a) && is_undetermined_type(t)) || continue
            return [t]
        elseif isa(a, PrimitiveCall)
            (get_body(mapp(v)) == get_body(mapp(a)) && args(v) == args(a) && !is_undetermined_type(t)) || continue
            return [t]
        end
    end

    return invoke(retrieve_type_from_usage, Tuple{APN,APN}, v, body)
end

function retrieve_type_from_usage(v::Var{ProductType}, body::AbstractCall)
    invoke(retrieve_type_from_usage, Tuple{Var{ProductType},APN,TypeContext}, v, body)
end

function retrieve_type_from_usage(v::Var{ProductType}, body::APN)
    field_types = map(i -> retrieve_type_from_usage(primitive_call(v, constant(i)), body),
        1:length(get_type(v)))
    any(isempty, field_types) && return []
    field_types = first.(field_types)
    new_type = ProductType(get_typename(get_type(v)), field_types, get_names(get_type(v)), meta(get_type(v)))
    return [new_type]
end =#

export TypeContext, inference, partial_inference, push_type!, pop_type!, push_var!, pop_var!

struct TypeContext
    name_to_type::Dict{Symbol,Vector{<:AbstractPCTType}}
    name_to_variable::Dict{Symbol,Vector}
end

get_name_to_type(context::TypeContext) = context.name_to_type
get_name_to_variable(context::TypeContext) = context.name_to_variable
function find_var_by_name(context::TypeContext, n::Symbol)
    d = get_name_to_variable(context)
    n_vars = get(d, n, [])
    !isempty(n_vars) && return last(n_vars)
    error("variable \"$(n)\" not found")
end

default_context() = TypeContext(
    Dict{Symbol,Vector{<:AbstractPCTType}}(
        :N => [N()],
        :I => [I()],
        :R => [R()],
        :C => [C()],
        :CV => [MapType(VecType([N()]), C())],
        :RV => [MapType(VecType([N()]), R())],
        :CF => [MapType(VecType([C()]), C())],
        :RF => [MapType(VecType([R()]), R())],
        :CM => [MapType(VecType([N(), N()]), C())],
        :RM => [MapType(VecType([N(), N()]), R())],
        :CO => [MapType(VecType([C(), C()]), C())],
        :RO => [MapType(VecType([R(), R()]), R())],
        :Her => [MapType(VecType([N(), N()]), C(), Dict(:symmetries => [
            pct_map(var(:A), pct_map(var(:i), var(:j), conjugate(call(var(:A), var(:j), var(:i))))),
        ]))],
        :Sym => [MapType(VecType([N(), N()]), R(), Dict(:symmetries => [
            pct_map(var(:A), pct_map(var(:i), var(:j), call(var(:A), var(:j), var(:i)))),
        ]))],
        :SSym => [MapType(VecType([N(), N()]), R(), Dict(:symmetries => [
            pct_map(var(:A), pct_map(var(:i), var(:j), mul(constant(-1), call(var(:A), var(:j), var(:i))))),
        ]))],
        :R4 => [MapType(VecType([N(), N(), N(), N()]), R())],
        :R3 => [MapType(VecType([N(), N(), N()]), R())],
        :C4 => [MapType(VecType([N(), N(), N(), N()]), C())],
        :C3 => [MapType(VecType([N(), N(), N()]), C())],
    ),
    Dict{Symbol,Vector{<:Var}}(
        :Infty => [infty()],
        :∞ => [infty()],
        :∇ => [nabla()],
    )
)

function TypeContext()
    context = default_context()
    push_var!(context, :_, var(:_, UndeterminedPCTType()))
    return context
end

Base.haskey(c::TypeContext, k) = haskey(get_name_to_type(c), k)
Base.getindex(c::TypeContext, k) = first(get_name_to_type(c)[k])

function push_type!(c::TypeContext, key::Symbol, type::AbstractPCTType; replace=false)
    if haskey(get_name_to_type(c), key)
        if replace
            get_name_to_type(c)[key][1] = type
        else
            pushfirst!(get_name_to_type(c)[key], type)
        end
    else
        get_name_to_type(c)[key] = Vector{AbstractPCTType}()
        push!(get_name_to_type(c)[key], type)
    end
    return type
end

function pop_type!(c::TypeContext, key::Symbol, value=nothing)
    haskey(get_name_to_type(c), key) || error("type $(key) is undefined.")
    popped = popfirst!(get_name_to_type(c)[key])
    value !== nothing && @assert value == popped
    return popped
end

function push_var!(c::TypeContext, key::Symbol, v::Var)
    list = get!(get_name_to_variable(c), key, [])
    push!(list, v)
end

function pop_var!(c::TypeContext, key::Symbol)
    haskey(get_name_to_variable(c), key) || error("variable $(key) is undefined")
    return pop!(get_name_to_variable(c)[key])
end

function get_var(c::TypeContext, key::Symbol)
    haskey(get_name_to_variable(c), key) || return nothing
    return last(get_name_to_variable(c)[key])
end

#= op_context!(v::Var, op!::Function, context::TypeContext) = op!(context, name(v), get_type(v))

function op_context!(vec::PCTVector, op!::Function, context::TypeContext)
    map(t -> op_context!(t, op!, context), content(vec))
end =#

inference(n::Any) = n

function check_parametric_type_capture!(bounds, body, context)
    free = get_free(body)

    for t in free
        t_type = get_type(get_var(context, name(t)))
        t_free = [get_free(t_type)...]
        i = findfirst(x->name(x) in name.(bounds), t_free) 
        i === nothing || error("shadowing type parameter $(pretty(t_free[i])) is not allowed.")
    end
end

function inference(n::T, context::TypeContext=TypeContext()) where {T<:APN}
    has_bound = any(f -> hasfield(T, f), bound_fields(T))
    if has_bound
        #= op_context!(get_bound(n), pct_push!, context) =#
        for b in content(get_bound(n))
            if get_type(b) == UndeterminedPCTType()
                b = set_type(b, N())
            end
            push_var!(context, get_body(b), b)
        end
        # the following line may be redundant.
        n = set_bound(n, map(t -> inference(t, context), [get_bound(n)])...)

        check_parametric_type_capture!(get_bound(n), get_body(n), context)
    end
    n = set_content(n, map(t -> inference(t, context), content(n))...)
    has_bound && map(b -> pop_var!(context, get_body(b)), content(get_bound(n)))
    # Setting the type may also be redundant.
    return set_type(n, partial_inference(typeof(n), terms(n)...))
end

function inference(v::Var, context::TypeContext)
    startswith(string(get_body(v)), "__") && return v
    new_v = find_var_by_name(context, name(v))
    return set_type(new_v, inference(get_type(new_v), context))
end

function inference(l::T, context::TypeContext) where {T<:AbstractLet}
    typed_bound, typed_args = [], []
    for (f, a) in zip(get_bound(l), args(l))
        a = inference(a, context)
        is_copy = isa(f, Copy)
        f = is_copy ? get_body(f) : f
        f = set_type(f, get_type(a))
        push!(typed_bound, is_copy ? pct_copy(f) : f)
        push!(typed_args, a)
        push_var!(context, get_body(f), f)
    end

    typed_content = inference(get_body(l), context)
    map(f -> pop_var!(context, isa(f, Copy) ? get_body(get_body(f)) : get_body(f)), typed_bound)
    return make_node(T, pct_vec(typed_bound...), pct_vec(typed_args...), typed_content)
end

inference(c::Constant, ::TypeContext) = set_type(c, partial_inference(Constant, terms(c)...))

function partial_inference(::Type{T}, terms...)::AbstractPCTType where {T<:PCTVector}
    return VecType(get_type.(collect(terms)))
end

function partial_inference(::Type{Map}, terms...)::AbstractPCTType
    bound, content = terms
    return MapType(get_type(bound), get_type(content))
end

function partial_inference(::Type{T}, ::PCTVector, ::Symbol)::AbstractPCTType where {T<:Var}
    UndeterminedPCTType()
end

function partial_inference(::Type{T}, terms...)::AbstractPCTType where {T<:AbstractCall}
    mapp = first(terms)
    if mapp == nabla()
        t = first(terms[2])
        return MapType(get_bound_type(get_type(t)), v_unwrap(get_bound_type(get_type(t))))
    end

    if isa(mapp, Var) && startswith(string(get_body(mapp)), "__")
        length(collect(terms)) != 2 && error("control function on more than one argument is not supported")
        return get_type(last(terms))
    end

    if isa(get_type(mapp), ParametricMapType)
        param_type = get_type(mapp)
        values = Dict()
        concrete_type = get_type(last(terms))
        parametric_type = get_bound_type(get_param_body(param_type))
        type_match!(
            get_params(param_type), values,
            parametric_type, concrete_type)

        return parametrize_type(param_type, [values[p] for p in get_params(param_type)]...) |> get_body_type
    end

    args = terms[2]
    if isa(get_type(mapp), MultiType)
        return convert_pct_type(Base.return_types(
            get_func_obj(get_type(mapp)),
            tuple(to_julia_type.(get_type.(args))...))[1])
    end

    return get_body_type(get_type(mapp))
end

function partial_inference(::Type{<:AbstractLet}, terms...)::AbstractPCTType
    return get_type(last(terms))
end


function partial_inference(::Type{T}, term::PCTVector)::AbstractPCTType where {T<:Union{Add,Mul}}
    @assert length(term) > 0
    return escalate(map(get_type, content(term))...)
end


function partial_inference(::Type{T}, terms...)::AbstractPCTType where {T<:Contraction}
    return get_type(last(terms))
end

function partial_inference(::Type{Prod}, terms...)::AbstractPCTType
    return get_type(last(terms))
end

function partial_inference(::Type{Conjugate}, term)::AbstractPCTType
    isa(get_type(term), ElementType) && return get_type(term)
    return MapType(VecType(reverse(get_content_type(get_bound_type(get_type(term))))), get_body_type(get_type(term)), meta(get_type(term)))
end

function partial_inference(::Type{Pullback}, mapp)::AbstractPCTType
    if isa(get_type(mapp), MapType)
        bound_type = get_bound_type(get_type(mapp))
        body_type = get_body_type(get_type(mapp))
        return MapType(add_content(bound_type, body_type), first(get_content_type(bound_type)))
    elseif isa(get_type(mapp), ParametricMapType)
        bound_type = get_bound_type(get_param_body(get_type(mapp)))
        body_type = get_body_type(get_param_body(get_type(mapp)))
        return ParametricMapType(
            get_params(get_type(mapp)),
            MapType(add_content(bound_type, body_type), first(get_content_type(bound_type))))
    else
        error("$(pretty(get_type(mapp))) is not supported")
    end
end

function partial_inference(::Type{PrimitivePullback}, v::APN)::AbstractPCTType
    get_type(v) == UndeterminedPCTType() && return UndeterminedPCTType()
    if isa(get_type(v), MapType)
        bound_type = get_bound_type(get_type(v))
        body_type = get_body_type(get_type(v))
        return MapType(add_content(bound_type, body_type), bound_type)
    else
        type_vars = get_params(get_type(v))
        m_type = get_param_body(get_type(v))
        bound_type = get_bound_type(m_type)
        body_type = get_body_type(m_type)
        return ParametricMapType(type_vars, MapType(add_content(bound_type, body_type), bound_type))

    end
end

function partial_inference(::Type{PrimitivePullback}, v::PCTVector)::AbstractPCTType
    return UndeterminedPCTType()
end


partial_inference(::Type{Constant}, ::Unsigned) = N()
partial_inference(::Type{Constant}, ::Int) = I()
partial_inference(::Type{Constant}, ::Real) = R()
partial_inference(::Type{Constant}, ::Complex) = C()

function partial_inference(::Type{T}, terms...)::AbstractPCTType where {T<:AbstractDelta}
    get_type(last(terms))
end


function partial_inference(::Type{IntDiv}, terms...)::AbstractPCTType
    return I()
end

function partial_inference(::Type{Monomial}, x::APN, power::APN)::AbstractPCTType

    base(get_type(x)) == C() && return C()
    return escalate(get_type(x), get_type(power), R())
end

inference(d::AbstractPCTType, ::TypeContext=TypeContext()) = d

# TODO: Properly implement the inference for MapType
#= function inference(d::MapType, context::TypeContext=TypeContext()) 
    new_bounds = VecType(map(t->inference(t, context), get_content_type(get_bound_type(d))))
    return MapType(new_bounds, inference(get_body_type(d), context))
end =#


function inference(v::VecType, context::TypeContext=TypeContext())
    new_vectype = VecType(map(t -> inference(t, context), get_content_type(v)))
    return new_vectype
end

function inference(m::MapType, context::TypeContext=TypeContext())
    inf_m = MapType(inference(get_bound_type(m), context), inference(get_body_type(m), context))
    if haskey(meta(m), :symmetries)
        new_symmetries = []
        for s in meta(m)[:symmetries]
            f = first(get_bound(s))
            indices = get_bound(get_body(s))
            body = get_body(get_body(s))

            f = set_type(f, inf_m)
            indices = map(set_type, indices, get_bound_type(inf_m))

            push!(new_symmetries, inference(pct_map(f, pct_map(indices..., body)), context))
        end
        meta(m)[:symmetries] = new_symmetries
    end

    new_maptype = MapType(get_bound_type(inf_m), get_body_type(inf_m), meta(m))
    return new_maptype
end

function inference(d::Domain, context::TypeContext=TypeContext())
    #= vars = vcat(variables(lower(d)), variables(upper(d))) =#
    #= for v in vars
        get_var(context, get_body(v)) === nothing || continue
        push_var!(context, get_body(v), set_type(v, base(d)))
    end =#

    new_domain = Domain(base(d),
        inference(lower(d), context),
        inference(upper(d), context),
        meta(d))
    return new_domain
end

function partial_inference(::Type{Composition}, term::PCTVector)
    length(term) == 0 && return UndeterminedPCTType()
    i = findfirst(t -> isa(get_type(t), ElementType) && get_type(t) != UndeterminedPCTType(), content(term))
    if i !== nothing
        error("Cannot add/subtract numbers with operators/matrices:
              $(pretty(term[i]))\n $(get_type(term[i]))")
    end
    bound_type = get_bound_type(get_type(first(content(term))))
    body_type = get_body_type(get_type(last(content(term))))
    return MapType(bound_type, body_type)
end

function partial_inference(::Type{RevComposition}, term::PCTVector)
    length(term) == 0 && return UndeterminedPCTType()
    bound_type = get_bound_type(get_type(last(content(term))))
    body_type = get_body_type(get_type(first(content(term))))
    return MapType(bound_type, body_type)
end

function partial_inference(::Type{T}, body::APN) where {T<:Univariate}
    return get_type(body)
end

function partial_inference(::Type{Fold}, terms...)
    _..., body = terms
    return get_type(body)
end

function partial_inference(::Type{Splat}, t::APN)
    return SplatType(get_type(t))
end

function partial_inference(::Type{ParametricMap}, terms...)
    return ParametricMapType([first(terms)...], get_type(last(terms)))
end

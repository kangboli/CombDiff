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
    return nothing
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
    free = get_free(inference(body, context))

    for t in free
        t_type = get_type(get_var(context, name(t)))
        t_free = [get_free(t_type)...]
        i = findfirst(x -> name(x) in name.(bounds), t_free)
        i === nothing || error("shadowing type parameter $(pretty(t_free[i])) is not allowed.")
    end
end


is_undetermined_type(t::AbstractPCTType) = false

is_undetermined_type(t::UndeterminedPCTType) = true
is_undetermined_type(t::MapType) = any(is_undetermined_type, [get_bound_type(t)..., get_body_type(t)])

function is_undetermined_type(t::AbstractVecType)
    return any(is_undetermined_type, get_content_type(t))
end

function inference(n::T, context::TypeContext=TypeContext()) where {T<:APN}
    has_bound = any(f -> hasfield(T, f), bound_fields(T))

    if has_bound
        #= op_context!(get_bound(n), pct_push!, context) =#
        for b in content(get_bound(n))
            b = set_type(b, inference(get_type(b), context))
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

function inference(n::PrimitiveCall, context::TypeContext=TypeContext())
    isa(mapp(n), Constructor) || return invoke(inference, Tuple{APN,TypeContext}, n, context)

    field_names = new_symbol(n; num=length(args(n)), symbol=:_s)
    new_args = map(t -> inference(t, context), args(n))
    m = set_type(mapp(n),
        MapType(VecType(get_type.(new_args)),
            ProductType(:__anonymous, get_type.(new_args), field_names)))
    return primitive_call(m, new_args...)
end


function inference(v::Var, context::TypeContext)
    new_v = find_var_by_name(context, name(v))
    if new_v !== nothing
        return set_type(new_v, inference(get_type(new_v), context))
    else
        constructor_type = first(get_name_to_type(context)[name(v)])
        #= return set_type(v, inference(derive_constructor_type(constructor_type), context)) =#
        return make_constructor(constructor_type)
    end
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

function partial_inference(::Type{T}, ::Any, ::Symbol)::AbstractPCTType where {T<:Var}
    UndeterminedPCTType()
end

function partial_inference(::Type{T}, terms...)::AbstractPCTType where {T<:AbstractCall}
    mapp = first(terms)
    if mapp == nabla()
        t = first(terms[2])
        return MapType(get_bound_type(get_type(t)), v_unwrap(get_bound_type(get_type(t))))
    end

    if isa(get_type(mapp), ParametricMapType)
        return get_return_type(mapp, last(terms))
        #= param_type = get_type(mapp)
        values = Dict()
        concrete_type = get_type(last(terms))
        parametric_type = get_bound_type(get_param_body(param_type))
        type_match!(
            get_params(param_type), values,
            parametric_type, concrete_type)

        return parametrize_type(param_type, [values[p] for p in get_params(param_type)]...) |> get_body_type =#
    end

    args = terms[2]
    if isa(get_type(mapp), MultiType)
        return convert_pct_type(Base.return_types(
            get_func_obj(get_type(mapp)),
            tuple(to_julia_type.(get_type.(args))...))[1])
    end

    return get_return_type(mapp, terms[end])
end

function partial_inference(::Type{ParametricVar}, mapp, args)
    return parametrize_type(get_type(mapp), args...)
end

function partial_inference(::Type{<:AbstractLet}, terms...)::AbstractPCTType
    return get_type(last(terms))
end


function partial_inference(::Type{T}, term)::AbstractPCTType where {T<:Union{Add,Mul}}
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
        return MapType(add_content(bound_type, body_type), v_unwrap(bound_type))
    elseif isa(get_type(mapp), ParametricMapType)
        bound_type = get_bound_type(get_param_body(get_type(mapp)))
        body_type = get_body_type(get_param_body(get_type(mapp)))
        return ParametricMapType(
            get_params(get_type(mapp)),
            MapType(add_content(bound_type, body_type), v_unwrap(bound_type)))
    else
        error("$(pretty(get_type(mapp))) is not supported")
    end
end

function partial_inference(::Type{PrimitivePullback}, v::APN)::AbstractPCTType
    get_type(v) == UndeterminedPCTType() && return UndeterminedPCTType()
    if isa(get_type(v), MapType)
        bound_type = get_bound_type(get_type(v))
        body_type = get_body_type(get_type(v))
        return MapType(add_content(bound_type, body_type), v_unwrap(bound_type))
    elseif isa(get_type(v), ParametricMapType)
        type_vars = get_params(get_type(v))
        m_type = get_param_body(get_type(v))
        bound_type = get_bound_type(m_type)
        body_type = get_body_type(m_type)
        return ParametricMapType(type_vars, MapType(add_content(bound_type, body_type), v_unwrap(bound_type)))
    elseif isa(get_type(v), ProductType)
        return UndeterminedPCTType()
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
    new_vectype = VecType(map(t -> inference(t, context), get_content_type(v)), meta(v))
    return new_vectype
end

function inference(v::ProductType, context::TypeContext=TypeContext())
    new_product_type = ProductType(get_typename(v), map(t -> inference(t, context), get_content_type(v)), get_names(v), meta(v))
    return new_product_type
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

function partial_inference(::Type{Dot}, predot, postdot)
    predot_type = get_type(predot)
    if isa(predot_type, MultiType)
        return MultiType(getfield(get_func_obj(predot_type), postdot))
        #= elseif isa(predot_type, VecType)
            i = findfirst(n -> n == terms[2], get_names(predot_type))
            return get_content_type(predot_type)[i] =#
    else
        return UndeterminedPCTType()
        #= error("accessing field of type $(predot_type) is not supported") =#
    end
end

function partial_inference(::Type{Constructor}, ::Symbol)
    return UndeterminedPCTType()
end

function partial_inference(::Type{Grad}, body::APN)
    maptype = get_type(body)
    maptype == UndeterminedPCTType() && return UndeterminedPCTType()
    if isa(maptype, MapType)
        input_types = get_bound_type(maptype)
        return MapType(input_types, input_types)
    else
        isa(maptype, ParametricMap)
        input_types = get_bound_type(get_param_body(maptype))

        return ParametricMapType(get_params(maptype), MapType(input_types, input_types))
    end
end

function partial_inference(::Type{FixedPoint}, body::APN)
    return v_unwrap(get_bound_type(get_type(body)))
end

function partial_inference(::Type{Jacobian}, body::APN)
    maptype = get_type(body)
    maptype == UndeterminedPCTType() && return UndeterminedPCTType()
    if isa(maptype, MapType)
        input_type = first(get_bound_type(maptype))
        in_bound = get_content_type(get_bound_type(input_type))
        return MapType(VecType([input_type]), MapType(VecType(repeat(in_bound, 2)), get_body_type(input_type)))
    else
        isa(maptype, ParametricMap)
        input_type = first(get_bound_type(get_param_body(maptype)))
        in_bound = get_content_type(get_bound_type(input_type))

        return ParametricMapType(get_params(maptype),
            MapType(VecType([input_type]), MapType(VecType(repeat(in_bound, 2)), get_body_type(input_type))))
        return
    end
end

function partial_inference(::Type{T}, mapp) where {T<:AbstractPushforward}
    if isa(get_type(mapp), MapType)
        bound_type = get_bound_type(get_type(mapp))
        body_type = get_body_type(get_type(mapp))
        return MapType(VecType([bound_type..., bound_type...]), body_type)
    elseif isa(get_type(mapp), ParametricMapType)
        bound_type = get_bound_type(get_param_body(get_type(mapp)))
        body_type = get_body_type(get_param_body(get_type(mapp)))
        return ParametricMapType(
            get_params(get_type(mapp)),
            MapType(VecType([bound_type..., bound_type...]), body_type))
    else
        error("$(pretty(get_type(mapp))) is not supported")
    end
end

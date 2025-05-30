export ParametricDomain, ParametricMapType, parametrize_type, ParametricProductType

struct ParametricDomain <: AbstractDomain
    parameters::Vector
    body::Domain
end

get_params(pd::ParametricDomain) = pd.parameters
get_param_body(pd::ParametricDomain) = pd.body
name(pd::ParametricDomain) = name(get_param_body(pd))

struct ParametricMapType <: AbstractMapType
    parameters::Vector
    body::MapType
end

get_params(pm::ParametricMapType) = pm.parameters
get_param_body(pm::ParametricMapType) = pm.body
name(pm::ParametricMapType) = name(get_param_body(pm))
linear(c::ParametricMapType) = false

struct ParametricProductType <: AbstractVecType
    parameters::Vector
    body::ProductType
end

get_params(pv::ParametricProductType) = pv.parameters
get_param_body(pv::ParametricProductType) = pv.body
name(pv::ParametricProductType) = name(get_param_body(pv))

function parametrize_type(t::T, args...) where {T<:Union{ParametricDomain,ParametricMapType,ParametricProductType}}
    args = [args...]
    append!(args, fill(infty(), length(get_params(t)) - length(args)))
    result = get_param_body(t)
    for (p, a) in zip(get_params(t), args)
        result = subst_type(result, p, a)
    end
    return result
end

parametrize_type(t::AbstractPCTType) = t

parametrize_type(::N, arg) = Domain(N(), constant(1), arg, Dict(:name => :N))

parametrize_type(::T, lower, upper) where {T<:ElementType} = Domain(T(), lower, upper, Dict(:name => Symbol(string(T))))

function parametrize_type(mt::MapType, type_args...)
    new_bounds = Vector{AbstractPCTType}()
    for i in 1:length(get_bound_type(mt))
        if i <= length(type_args)
            push!(new_bounds, parametrize_type(get_bound_type(mt)[i], type_args[i]))
        else
            push!(new_bounds, get_bound_type(mt)[i])
        end
    end
    #= parametrized = map(parametrize_type, get_content_type(get_bound_type(mt)), collect(type_args)) =#

    return MapType(VecType(new_bounds), get_body_type(mt), meta(mt))
end


#= function parametrize_type(::N, args...) 
    length(args) == 1 && return Domain(N(), constant(1), first(args))
    length(args) == 2 && return Domain(N(), args...)
    return N()
end


function parametrize_type(::T, args...)  where T <: ElementType
    length(args) == 2 && return Domain(T(), args...)
    return T()
end =#

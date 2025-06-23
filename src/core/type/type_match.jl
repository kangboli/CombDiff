
function type_match!(::Vector, ::Dict, ::S, ::T) where {S<:AbstractPCTType,T<:AbstractPCTType}
    error("trying to match different types: $(S) and $(T)")
end


function type_match!(parameters::Vector, values::Dict,
    parametric::T, concrete::T) where {T<:AbstractVecType}

    for (x, y) in zip(get_content_type(parametric), get_content_type(concrete))
        type_match!(parameters, values, x, y)
    end
    return values
end

function type_match!(parameters::Vector, values::Dict,
    parametric::MapType, concrete::MapType)

    type_match!(parameters, values, get_bound_type(parametric), get_bound_type(concrete))
    #= type_match!(parameters, values, get_body_type(parametric), get_body_type(concrete)) =#

    return values
end

function type_match!(parameters::Vector, values::Dict,
    parametric::Domain, concrete::Domain)

    type_match!(parameters, values, upper(parametric), upper(concrete))
    type_match!(parameters, values, lower(parametric), lower(concrete))

    return values
end
function type_match!(parameters::Vector, values::Dict,
    parametric::PCTVector, concrete::APN)

    for (p, c) in zip(content(parametric), content(concrete))
        type_match!(parameters, values, p, c)
    end
    return values
end

function type_match!(parameters::Vector, values::Dict,
    parametric::T, concrete::S) where {T<:APN,S<:APN}

    i = findfirst(p -> name(p) in name.(get_free(parametric)), parameters)
    i === nothing && return values
    T <: Var || error("$(pretty(parametric)): Arithmatics in type parameters not yet supported.")

    p = parameters[i]
    haskey(values, p) && (@assert values[p] == concrete)

    values[p] = concrete
    return values
end

function type_match!(_::Vector, values::Dict, ::T, ::T) where {T<:ElementType}
    return values
end

function type_match!(::Vector, values::Dict, ::S, ::T) where {S<:ElementType,T<:ElementType}
    return values
end

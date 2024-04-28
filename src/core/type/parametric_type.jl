export ParametricDomain, ParametricMapType, parametrize_type

struct ParametricDomain <: AbstractDomain
    parameters::Vector
    body::Domain
end

get_params(pd::ParametricDomain) = pd.parameters
get_param_body(pd::ParametricDomain) = pd.body

struct ParametricMapType <: AbstractMapType
    paramters::Vector
    body::MapType
end

get_params(pm::ParametricMapType) = pm.paramters
get_param_body(pd::ParametricMapType) = pd.body

function param_subst(p::Domain, old::Vector, new::Vector)
    new_upper = ecall(pct_map(old..., upper(p)), new...)
    new_lower = ecall(pct_map(old..., lower(p)), new...)
    return Domain(
        base(p), new_lower, new_upper, meta(p))
end
function param_subst(p::MapType, old::Vector, new::Vector)

    new_bounds = map(get_content_type(get_bound_type(p))) do bound
        param_subst(bound, old, new)
    end |> VecType

    new_body = param_subst(get_body_type(p), old, new)

    return MapType(new_bounds, new_body, meta(p))
end

function parametrize_type(t::T, args...) where {T <: Union{ParametricDomain, ParametricMapType}}
    return param_subst(get_param_body(t), get_params(t), [args...])
end


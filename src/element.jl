export
    make_node,
    content,
    set_content,
    terms,
    set_terms,
    set_bound,
    get_bound,
    mul,
    monomial,
    add,
    get_type,
    mapp,
    args,
    name,
    var,
    set_type,
    base,
    power,
    call,
    set_i,
    pct_vec,
    pct_product,
    is_univariate,
    pct_map,
    pct_sum,
    pct_int,
    flatten_add,
    flatten_mul,
    constant,
    delta,
    delta_not,
    conjugate,
    pullback,
    signatures!


term_start(n::APN) = 2

"""
    make_node(T, terms...,
                type=UndeterminedPCTType())

This function is the gate way for creating all nodes.
The purpose is to ensure at construction that
1. the node is typed (through inference).
2. the node is canonical within its e-class.

"""
function make_node(::Type{T}, terms::Vararg;
    type=UndeterminedPCTType()
) where {T<:APN}

    S, terms, t = e_class_reduction(T, terms...)
    type == UndeterminedPCTType() && (type = t)
    return S(type, terms...)
end

"""
    get_type(n)

Return the PCT type of `n`.
"""
get_type(n::APN)::AbstractPCTType = n.type


"""
    set_type(n)

Set the PCT type of `n` and return a new copy.
"""
function set_type(n::T, new_type) where {T<:APN}
    return make_node(T, terms(n)..., type=new_type)
end

"""
    terms(n)

Get the subterms of `n`.
"""
terms(n::T) where {T<:APN} = map(f -> getfield(n, f), fieldnames(T)[term_start(n):end])

"""
    set_terms(n)

Set the subterms of `n`.
"""
function set_terms(::T, new_terms...) where {T<:APN}
    make_node(T, new_terms...)
end


"""
    bound_fields(T)

Return the names of fields in `T` that is considered part of `bound`.
"""
bound_fields(::Type{T}) where {T<:APN} = [:bound]

"""
    content_fields(T)

Return the names of fields in `T` that is considered part of `content`.
"""
content_fields(::Type{T}) where {T<:APN} = [:body]

# """
#     ff(n)

# Get the first field that is considered bound.
# """
# ff(n::APN) = first(bound(n))

content(n::T) where {T<:APN} = map(f -> getfield(n, f), filter(f -> hasfield(T, f), content_fields(T)))

function set_pct_fields(n::T, fields::Vector{Symbol}, values...) where {T<:APN}
    isempty(values) && return n
    d = Dict(zip(fields, [values...]))
    take_field(f::Symbol) = get(d, f, getfield(n, f))
    return set_terms(n, take_field.(fieldnames(T)[term_start(n):end])...)
end

function set_content(n::T, new_content...) where {T<:APN}
    set_pct_fields(n, content_fields(T), new_content...)
end

function set_bound(n::T, new_bound...) where {T<:APN}
    set_pct_fields(n, bound_fields(T), new_bound...)
end

base(n::APN) = n
power(::APN) = make_node(Constant, 1)


function set_type(n::Var{S}, new_type) where {S<:AbstractPCTType}
    return make_node(Var, terms(n)..., type=new_type)
end

function set_terms(n::T, new_terms...) where {T<:Var}
    make_node(T, new_terms...; type=get_type(n))
end

function set_type(n::PCTVector, new_type)
    return make_node(PCTVector, terms(n)..., type=new_type)
end

function set_content(v::PCTVector, new_content...)
    return make_node(PCTVector, new_content...; type=get_type(v))
end

function set_terms(v::PCTVector, new_terms...)
    return set_content(v, new_terms...)
end

symmetric(d::Domain) = haskey(d.meta, :symmetric) && d.meta[:symmetric]
symmetric(::ElementType) = false
symmetric(v::Var) = symmetric(get_type(v))

is_periodic(d::Domain) = haskey(d.meta, :periodic) && d.meta[:periodic]
is_periodic(::ElementType) = false

is_contractable(d::Domain) = !haskey(d.meta, :contractable) || d.meta[:contractable]
is_contractable(::ElementType) = true
is_contractable(v::Var) = is_contractable(get_type(v))
is_contractable(v::MapType) = true


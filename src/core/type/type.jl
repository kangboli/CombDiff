export AbstractPCTType,
    get_body_type,
    MapType,
    MultiType,
    VecType,
    N,
    I,
    R,
    C,
    Domain,
    symmetries,
    ProductType,
    lower,
    upper,
    UndeterminedPCTType,
    symmetric,
    get_bound_type

abstract type AbstractPCTType end
abstract type AbstractSignatureTree end

"""
The most general and abstract node that represents anything in the theory.
"""
abstract type AbstractPCTNode end
const APN = AbstractPCTNode

abstract type AbstractMapType <: AbstractPCTType end

abstract type AbstractVecType <: AbstractMapType end

abstract type ElementType <: AbstractPCTType end
struct UndeterminedPCTType <: ElementType end
get_body_type(::UndeterminedPCTType) = UndeterminedPCTType()
get_bound_type(::UndeterminedPCTType) = VecType([])
get_content_type(::UndeterminedPCTType) = UndeterminedPCTType()

struct I <: ElementType end
struct R <: ElementType end
struct C <: ElementType end
struct N <: ElementType end

base(::T) where {T<:ElementType} = T()
lower(::ElementType) = minfty()
lower(::N) = constant(1)
upper(::ElementType) = infty()

abstract type AbstractDomain <: ElementType end

struct Domain <: AbstractDomain
    base::ElementType
    lower::APN
    upper::APN
    meta::Dict
end

Domain(base::ElementType, lower::APN, upper::APN; meta=Dict()) =
    Domain(base, lower, upper, meta)


struct ProductType <: AbstractVecType
    typename::Symbol
    content::Vector{AbstractPCTType}
    names::Vector{Symbol}
    meta::Dict
end

ProductType(typename, content, names) = ProductType(typename, content, names, Dict())
get_names(p::ProductType) = p.names
get_typename(p::ProductType) = p.typename

function product_type_from_vec(v::Vector)
    return ProductType(:__anonymous, get_type.(v), name.(v))
end

function derive_constructor_type(p::ProductType)
    return MapType(VecType(get_content_type(p)), p)
end

function make_constructor(p::ProductType)
    Constructor(derive_constructor_type(p), get_typename(p))
end

function set_i(p::ProductType, i, new_item)
    replace_item(j::Integer) = i == j ? new_item : get_content_type(p)[j]
    return ProductType(
        get_typename(p),
        map(replace_item, 1:length(p)),
        get_names(p),
        meta(p)
    )
end

"""
    name(d)

The name of the domain. Saved mainly for cosmetic purposes
during printing.
"""
name(d::Domain) = meta(d)[:name]

base(d::Domain) = d.base
lower(d::Domain) = d.lower
upper(d::Domain) = d.upper

meta(m::Domain) = m.meta
meta(m::AbstractPCTType) = m.meta

function tensorize(m::Domain)
    base(m) == N()
    #= haskey(m.meta, :tensorize) && return m.meta[:tensorize] =#
end

tensorize(t::AbstractPCTType) = false
tensorize(t::N) = true

struct VecType <: AbstractVecType
    content::Vector{AbstractPCTType}
    meta::Dict
end

VecType(content) = VecType(content, Dict())
get_content_type(v::AbstractVecType) = v.content
get_bound_type(::AbstractVecType) = VecType([N()])
Base.length(v::AbstractVecType) = length(get_content_type(v))
Base.getindex(v::AbstractVecType, i::Int) = get_content_type(v)[i]
add_content(v::VecType, t::AbstractPCTType) = VecType(push!(copy(get_content_type(v)), t))

struct SplatType <: AbstractPCTType
    body::VecType
end


struct MapType <: AbstractMapType
    bound::VecType
    body::AbstractPCTType
    meta::Dict
end

get_bound_type(m::MapType) = m.bound
get_body_type(m::AbstractPCTType) = m.body

MapType(bound::VecType, content::AbstractPCTType) = MapType(bound, content, Dict())
MapType(bound::APN, content::AbstractPCTType) = MapType(VecType([bound]), content, Dict())

type_based(a::Domain, b::ElementType) = a.base == b
type_based(a::ElementType, b::ElementType) = a == b

# Refuse the type inference for complicated types for now.
type_based(a::MapType, ::ElementType) = false
type_based(a::VecType, ::ElementType) = false
type_based(a::ProductType, ::ElementType) = false
type_based(a::SplatType, e::ElementType) = type_based(get_body_type(a), e)

symmetries(c::MapType) = get(c.meta, :symmetries, [])

linear(c::MapType) = get(c.meta, :linear, false)

function escalate(element_types::Vararg)
    UndeterminedPCTType() in element_types && return UndeterminedPCTType()
    any(t -> type_based(t, C()), element_types) && return C()
    any(t -> type_based(t, R()), element_types) && return R()
    any(t -> type_based(t, I()), element_types) && return I()
    any(t -> type_based(t, N()), element_types) && return N()
    if any(t -> isa(t, FermionicState), element_types)
        @assert all(t -> isa(t, FermionicState), element_types)
        return FermionicState()
    end
    return UndeterminedPCTType()
end

function escalate(map_types::Vararg{MapType})
    # TODO: implement this properly
    bound_types = get_bound_type.(map_types)
    body_type = get_body_type.(map_types)
    #= @assert reduce(isequal, base.(bound_types)) =#
    return MapType(first(bound_types), escalate(body_type...))
end


struct MultiType <: AbstractPCTType
    func_obj
end

get_func_obj(m::MultiType) = m.func_obj
#= get_maptypes(m::MultiType) = m.maptypes =#
meta(::MultiType) = Dict()


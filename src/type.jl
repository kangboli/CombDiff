export AbstractPCTType,
    get_body_type,
    MapType,
    VecType,
    N,
    I,
    R,
    C,
    Domain,
    symmetries,
    VecType,
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

struct Domain <: ElementType
    base::ElementType
    lower::APN
    upper::APN
    meta::Dict
end

Domain(base::ElementType, lower::APN, upper::APN; meta=Dict()) =
    Domain(base, lower, upper, meta)

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

function Base.show(io::IO, ::MIME"text/plain", d::Domain)
    print(io, "$(name(d))∈$(verbose(base(d))):[$(pretty(lower(d))), $(pretty(upper(d)))]")
end

struct VecType <: AbstractPCTType
    content::Vector{AbstractPCTType}
end

get_content_type(v::VecType) = v.content
Base.length(v::VecType) = length(get_content_type(v))
Base.getindex(v::VecType, i::Int) = get_content_type(v)[i]
add_content(v::VecType, t::AbstractPCTType) = VecType(push!(copy(get_content_type(v)), t))


struct MapType <: AbstractPCTType
    bound::VecType
    body::AbstractPCTType
    meta::Dict
end

get_bound_type(m::MapType) = m.bound
get_body_type(m::MapType) = m.body

MapType(bound::VecType, content::AbstractPCTType) = MapType(bound, content, Dict())
MapType(bound::APN, content::AbstractPCTType) = MapType(VecType([bound]), content, Dict())

type_based(a::Domain, b::ElementType) = a.base == b
type_based(a::ElementType, b::ElementType) = a == b

symmetries(c::MapType) = get(c.meta, :symmetries, [])

linear(c::MapType) = get(c.meta, :linear, false)

function escalate(element_types::Vararg{T}) where {T<:ElementType}
    UndeterminedPCTType() in element_types && return UndeterminedPCTType()
    any(t -> type_based(t, C()), element_types) && return C()
    any(t -> type_based(t, R()), element_types) && return R()
    any(t -> type_based(t, I()), element_types) && return I()
    any(t -> type_based(t, N()), element_types) && return N()
    return UndeterminedPCTType()
end

function escalate(map_types::Vararg)
    # TODO implement this properly
    return first(map_types)
end



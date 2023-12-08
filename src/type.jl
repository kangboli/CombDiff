export AbstractPCTType, MapType, VecType, I, R, C, Domain, symmetries, VecType, lower, upper, UndeterminedPCTType, symmetric

abstract type AbstractPCTType end
abstract type AbstractSignatureTree end

"""
The most general and abstract node that represents anything in the theory.
"""
abstract type AbstractPCTNode end
const APN = AbstractPCTNode

abstract type ElementType <: AbstractPCTType end
struct UndeterminedPCTType <: ElementType end
content(::UndeterminedPCTType) = UndeterminedPCTType()
from(::UndeterminedPCTType) = UndeterminedPCTType()

struct I <: ElementType end
struct R <: ElementType end
struct C <: ElementType end

base(::T) where T <: ElementType = T()

struct Domain <: ElementType
    base::ElementType
    lower::APN
    upper::APN
    meta::Dict
end

Domain(base::ElementType, lower::APN, upper::APN; meta=Dict()) = 
    Domain(base, lower, upper, meta) 

function symmetric(d::Domain)
    #TODO: Use equivalence instead of equality.
    if isa(d.lower, Mul)
        return d.lower == mul(constant(-1), d.upper)
    else
        return mul(constant(-1), d.lower) == d.upper
    end
end

symmetric(::ElementType) = false

is_periodic(d::Domain) = haskey(d.meta, :periodic) && (d.meta[:periodic] == true)
is_periodic(::ElementType) = false


function is_contractable(d::Domain) 
    if haskey(d.meta, :contractable) 
        return d.meta[:contractable]
    end
    true
end

is_contractable(::ElementType) = true

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

content(v::VecType) = v.content
Base.length(v::VecType) = length(content(v))
Base.getindex(v::VecType, i::Int) = content(v)[i]
fc(v::VecType) = first(content(v))
add_content(v::VecType, t::AbstractPCTType) = VecType(push!(copy(content(v)), t))


struct MapType <: AbstractPCTType 
    from::VecType
    content::AbstractPCTType
    meta::Dict
end

from(m::MapType) = m.from
content(m::MapType) = m.content

MapType(from::VecType, content::AbstractPCTType) = MapType(from, content, Dict())
MapType(from::APN, content::AbstractPCTType) = MapType(VecType([from]), content, Dict())

type_based(a::Domain, b::ElementType) = a.base == b
type_based(a::ElementType, b::ElementType) = a == b

function symmetries(c::MapType)
    haskey(c.meta, :symmetries) || return []
    return c.meta[:symmetries]
end


function escalate(element_types::Vararg) 
    UndeterminedPCTType() in element_types && return UndeterminedPCTType()
    any(t->type_based(t, C()), element_types) && return C()
    any(t->type_based(t, R()), element_types) && return R()
    any(t->type_based(t, I()), element_types) && return I()
    return UndeterminedPCTType()
end


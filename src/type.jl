export AbstractPCTType, MapType, VecType, I, R, C, Domain, symmetries, VecType, lower, upper, UndeterminedPCTType, symmetric

abstract type AbstractPCTType end

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

Domain(base::ElementType, lower::APN, upper::APN) = 
    Domain(base, lower, upper, Dict()) 

function symmetric(d::Domain)
    #TODO: Use equivalence instead of equality.
    if isa(d.lower, Mul)
        return d.lower == mul(constant(-1), d.upper)
    else
        return mul(constant(-1), d.lower) == d.upper
    end
end

symmetric(::ElementType) = false

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

#= function Base.append!(v_1::VecType, rest::Vararg{VecType})
    append!(content(v_1), content.([rest...])...)
    return v_1
end

function Base.push!(v_1::VecType, e::AbstractPCTType)
    push!(content(v_1), e)
    return v_1
end =#


struct MapType <: AbstractPCTType 
    from::VecType
    content::AbstractPCTType
    meta::Dict
end

from(m::MapType) = m.from
content(m::MapType) = m.content

MapType(from, content) = MapType(from, content, Dict())

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
end


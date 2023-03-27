export AbstractPCTType, MapType, VecType, I, R, C

abstract type AbstractPCTType end

abstract type ElementType <: AbstractPCTType end
struct UndeterminedPCTType <: ElementType end
content(::UndeterminedPCTType) = UndeterminedPCTType()
from(::UndeterminedPCTType) = UndeterminedPCTType()

struct I <: ElementType end
struct R <: ElementType end
struct C <: ElementType end

struct Domain{T} <: ElementType
    upper::Number
    lower::Number
end

meta(m::AbstractPCTType) = m.meta

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
to(m::MapType) = m.content
content(m::MapType) = m.content

MapType(from, content) = MapType(from, content, Dict())

function escalate(element_types::Vararg) 
    UndeterminedPCTType() in element_types && return UndeterminedPCTType()
    C() in element_types && return C()
    R() in element_types && return R()
    I() in element_types && return I()
end


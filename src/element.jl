export Var, Map, AbstractCall, PrimitiveCall, Sum, Call, Let, Delta, make_node!, Conjugate, Mul, Pullback, Constant, Add, terms, set_content!, set_terms!, PCTVector, fc, ff

"""
The most general and abstract node that represents anything in the theory.
"""
abstract type AbstractPCTNode end
const APN = AbstractPCTNode

"""
The root of the AST. Serves as the default parent node.
"""
struct Origin <: APN end

"""
    make_node!(T, terms...,
                type=partial_inference(T, terms...),
                meta=Dict(:sup_node=>Origin()))

The interface for creating a node given its subterms.
It roughly does three things
1. Infer its type based on the subterms. If the subterms are not typed, the new node won't be typed either.
2. Create a new node and set the parent of the subterms to the new node.
3. Set the parent of the new node to `Origin()`.

All other functions that create new nodes should call this function.
"""
function make_node!(::Type{T}, terms::Vararg;
                    type=partial_inference(T, terms...), 
                    meta=Dict{Symbol, APN}(:sup_node => Origin())) where {T<:APN}
    node = T(type, meta, terms...)
    map(t -> set_sup_node!(t, node), terms)
    return node
end

"""
    get_type(n)

Return the PCT type of `n`.
"""
get_type(n::APN) = n.type


"""
    set_type(n)

Set the PCT type of `n` and return a new copy.
"""
function set_type(n::T, new_type) where {T<:APN}
    return make_node!(T, terms(n)..., type=new_type, meta=meta(n))
end

"""
    terms(n)

Get the subterms of `n`.
"""
terms(n::T) where {T<:APN} = map(f -> getfield(n, f), fieldnames(T)[3:end])

"""
    set_terms!(n)

Set the subterms of `n`.
"""
function set_terms!(n::T, new_terms...)::T where {T<:APN}
    make_node!(T, new_terms...; type=get_type(n), meta=meta(n))
end

"""
    from_fields(T)

Return the names of fields in `T` that is considered part of `from`.
"""
from_fields(::Type{T}) where {T<:APN} = [:from]

"""
    content_fields(T)

Return the names of fields in `T` that is considered part of `content`.
"""
content_fields(::Type{T}) where {T<:APN} = [:content]

from(n::T) where {T<:APN} = map(f -> getfield(n, f), filter(f -> hasfield(T, f), from_fields(T)))
ff(n::APN) = first(from(n))

content(n::T) where {T<:APN} = map(f -> getfield(n, f), filter(f -> hasfield(T, f), content_fields(T)))
fc(n::APN) = first(content(n))

function set_pct_fields!(n::T, fields::Vector{Symbol}, values...)::T where {T<:APN}
    isempty(values) && return n
    d = Dict(zip(fields, [values...]))
    take_field(f::Symbol) = get(d, f, getfield(n, f))
    return set_terms!(n, take_field.(fieldnames(T)[3:end])...)
end

function set_content!(n::T, new_content...)::T where {T<:APN}
    set_pct_fields!(n, content_fields(T), new_content...)
end

function set_from!(n::T, new_from...)::T where {T<:APN}
    set_pct_fields!(n, from_fields(T), new_from...)
end

meta(n::APN) = n.meta

sup_node(n::APN) = meta(n)[:sup_node]
set_sup_node!(n::APN, sup_node::APN) = meta(n)[:sup_node] = sup_node

abstract type TerminalNode <: APN end

set_sup_node!(::Any, ::TerminalNode) = nothing

mutable struct Var <: TerminalNode
    type::AbstractPCTType
    meta::Dict
    content::Symbol
end

name(v::Var) = v.content

struct PCTVector <: APN
    type::AbstractPCTType
    meta::Dict
    content::Vector
    function PCTVector(type::AbstractPCTType, meta::Dict, content::Vararg)
        new(type, meta, [content...])
    end
end

function Base.map(f::Function, v::PCTVector) 
    make_node!(PCTVector,  map(f, content(v))...;type=get_type(v), meta=meta(v))
end
Base.getindex(v::PCTVector, indices::Any) = set_content!(v, content(v)[indices])
Base.first(v::PCTVector) = first(content(v))
Base.last(v::PCTVector) = last(content(v))
Base.length(v::PCTVector) = length(content(v))

function set_content!(v::PCTVector, new_content...)
    return make_node!(PCTVector, new_content...;type =get_type(v), meta=meta(v))
end

function set_terms!(v::PCTVector, new_terms...)
    return set_content!(v, new_terms...) 
end

content(v::PCTVector) = v.content
terms(v::PCTVector) = content(v)

abstract type AbstractMap <: APN end

struct Map <: AbstractMap
    type::AbstractPCTType
    meta::Dict
    from::PCTVector
    content::APN
end

to(m::AbstractMap) = content(m)

function is_univariate(m::AbstractMap) 
    params = ff(m)
    length(params) == 1 &&
    isa(get_type(fc(params)), ElementType)
end

abstract type AbstractPullback <: AbstractMap end
abstract type AbstractCall <: APN end

mapp(c::AbstractCall) = c.mapp
args(c::AbstractCall) = c.args

content_fields(::Type{T}) where T <: AbstractCall = [:mapp, :args]

struct Call <: AbstractCall
    type::AbstractPCTType
    meta::Dict
    mapp::AbstractMap
    args::PCTVector
end

struct PrimitiveCall <: AbstractCall
    type::AbstractPCTType
    meta::Dict
    mapp::Union{Var, AbstractPullback}
    args::PCTVector
end

abstract type BuiltinFunction <: APN end

struct Cos <: BuiltinFunction
    type::MapType
    meta::Dict
    content::APN
end

struct Sin <: BuiltinFunction
    type::MapType
    meta::Dict
    content::APN
end

struct Exp <: BuiltinFunction
    type::MapType
    meta::Dict
    content::APN
end

struct Monomial <: APN
    type::AbstractPCTType
    meta::Dict
    base::APN
    power::APN
end

content_fields(::Type{Monomial}) = [:base, :power]


struct Add <: APN
    type::AbstractPCTType
    meta::Dict
    content::PCTVector
end


struct Mul <: APN
    type::AbstractPCTType
    meta::Dict
    content::PCTVector
end

function split_constant(m::Mul)
    consts = filter(t -> isa(t, Constant), content(m))
    non_consts = filter(t -> !isa(t, Constant), content(m))
    c = isempty(consts) ? make_node!(Constant, 1) : make_node!(Constant, prod(content.(consts)))
    n = isempty(non_consts) ? make_node!(Constant, 1) : make_node!(Mul, non_consts)
    return c, n
end


abstract type Contraction <: APN end

struct Sum <: Contraction
    type::AbstractPCTType
    meta::Dict
    from::PCTVector
    content::APN
    function Sum(type, meta, from::PCTVector, summand::APN)
        if !all(t->get_type(t) == I(), content(from)) 
            from = set_content!(from, map(t->set_type(t, I()), content(from))...) 
        end
        new(type, meta, from, summand)
    end
end

struct Integral <: Contraction
    type::AbstractPCTType
    meta::Dict
    from::PCTVector
    content::APN
    function Integral(type, meta, from::PCTVector, integrand::APN)
        if !all(t->get_type(t) == R(), content(from)) 
            from = set_content!(from, map(t->set_type(t, R()), content(from))...) 
        end
        new(type, meta, from, integrand)
    end
end

struct Prod <: APN
    type::AbstractPCTType
    meta::Dict
    from::PCTVector
    content::APN
end

abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

# from_fields(::Type{AbstractDelta}) = [:upper, :lower]
content_fields(::Type{T}) where T <: AbstractDelta = [:upper, :lower, :content]

struct Delta <: AbstractDelta
    type::AbstractPCTType
    meta::Dict
    upper::PCTVector
    lower::PCTVector
    content::APN
end

struct DeltaNot <: AbstractDelta
    type::AbstractPCTType
    meta::Dict
    upper::PCTVector
    lower::PCTVector
    content::APN
end



struct Conjugate <: APN
    type::AbstractPCTType
    meta::Dict
    content::APN
    #= function Conjugate(type::ElementType, meta::Dict, content::APN)
        (type == I() || type == R()) && return content
        return new(type, meta, content)
    end =#
end

function make_node!(::Type{Conjugate}, term;
                    type=get_type(term),
                    meta=Dict{Symbol, APN}(:sup_node => Origin()))
    type == I() || type == R() && return term
    node = Conjugate(type, meta, term)
    set_sup_node!(term, node)
    return node
end




struct Constant <: TerminalNode
    type::AbstractPCTType
    meta::Dict
    content::Number
end

struct Let <: APN
    type::AbstractPCTType
    meta::Dict
    substitutions::Vector{Pair{Var,<:APN}}
    content::APN
end

substitutions(l::Let) = l.substitutions


struct Pullback <: AbstractPullback
    type::AbstractPCTType
    meta::Dict
    content::AbstractMap
end

struct PrimitivePullback <: AbstractPullback
    type::AbstractPCTType
    meta::Dict
    content::Union{Var, PrimitivePullback}
end

struct Negate <: APN
    type::AbstractPCTType
    meta::Dict
    content::APN
end



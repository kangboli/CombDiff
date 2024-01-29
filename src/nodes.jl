export
    APN,
    Let,
    Var,
    Map,
    AbstractCall,
    PrimitiveCall,
    Call,
    Sum,
    Integral,
    Prod,
    Delta,
    DeltaNot,
    Monomial,
    Conjugate,
    Mul,
    Pullback,
    PrimitivePullback,
    Constant,
    Add,
    PCTVector,
    Negate

abstract type TerminalNode <: APN end

struct PCTVector <: APN
    type::VecType
    content::Vector
    function PCTVector(type::VecType, content::Vararg)
        new(type, [content...])
    end
end

pct_vec(content::Vararg{APN}) = make_node(PCTVector, content...)
Base.lastindex(v::PCTVector) = lastindex(v.content)
function Base.map(f::Function, v::PCTVector)
    make_node(PCTVector, map(f, content(v))...; type=get_type(v))
end
Base.setindex(v::PCTVector, indices::Any) = set_content(v, content(v)[indices]...)
Base.getindex(v::PCTVector, indices::Integer) = content(v)[indices]
Base.getindex(v::PCTVector, indices::Any) = make_node(PCTVector, content(v)[indices]...)
Base.first(v::PCTVector) = first(content(v))
Base.last(v::PCTVector) = last(content(v))
Base.length(v::PCTVector) = length(content(v))


function Base.iterate(v::Union{PCTVector,VecType})
    isempty(content(v)) && return nothing
    return content(v)[1], 2
end

function Base.iterate(v::Union{PCTVector,VecType}, state::Int)
    state > length(v) && return nothing
    return content(v)[state], state + 1
end

function set_i(v::PCTVector, i::Integer, new_item::APN)
    replace_item(j::Integer) = i == j ? new_item : v[j]
    set_content(v, replace_item.(1:length(v))...)
end

# TODO: Get rid of this
function remove_i(v::PCTVector, i::Integer)

    new = Vector{APN}()
    for (j, t) in enumerate(content(v))
        j == i && continue
        push!(new, t)
    end

    return pct_vec(new...)
end

content(v::PCTVector) = v.content
Base.isempty(v::PCTVector) = isempty(content(v))
terms(v::PCTVector) = content(v)

mutable struct Var{T<:AbstractPCTType} <: TerminalNode
    type::T
    range::PCTVector
    content::Symbol
end

name(v::Var) = v.content
range(v::Var) = v.range
var(s::Symbol, type=UndeterminedPCTType()) = make_node(Var, pct_vec(), s; type=type)
var(range::PCTVector, s::Symbol, type=UndeterminedPCTType()) = make_node(Var, range, s; type=type)

struct Conjugate <: APN
    type::AbstractPCTType
    content::APN
end

conjugate(term::APN) = make_node(Conjugate, term)

abstract type AbstractMap <: APN end

struct Map <: AbstractMap
    type::AbstractPCTType
    from::PCTVector
    content::APN
end

function pct_map(from_content::Vararg{APN})
    from_content = collect(from_content)
    make_node(Map, pct_vec(from_content[1:end-1]...), last(from_content))
end

function is_univariate(m::AbstractMap)
    params = ff(m)
    length(params) == 1 &&
        isa(get_type(fc(params)), ElementType)
end

abstract type AbstractPullback <: AbstractMap end

struct Pullback <: AbstractPullback
    type::AbstractPCTType
    content::AbstractMap
end

pullback(map::Map) = make_node(Pullback, map)

struct PrimitivePullback <: AbstractPullback
    type::AbstractPCTType
    content::APN
end

pullback(map::Union{Var,PCTVector}) = make_node(PrimitivePullback, map)
# TODO: Figure out the right pattern for a map to be a primitive one instead of 
# asuuming that the caller knows it.
primitive_pullback(n::APN) = make_node(PrimitivePullback, n)

abstract type AbstractCall <: APN end

mapp(c::AbstractCall) = c.mapp
args(c::AbstractCall) = c.args

content_fields(::Type{T}) where {T<:AbstractCall} = [:mapp, :args]

struct Call <: AbstractCall
    type::AbstractPCTType
    mapp::Union{Map,Pullback}
    args::PCTVector
end

function call(mapp::Union{Map,Pullback}, args::Vararg{<:APN})
    make_node(Call, mapp, make_node(PCTVector, args...))
end

struct PrimitiveCall <: AbstractCall
    type::AbstractPCTType
    mapp::APN
    args::PCTVector
end

function call(mapp::Union{Conjugate,Var,PrimitivePullback,PrimitiveCall}, args::Vararg{<:APN})
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end

struct Exp <: APN
    type::AbstractPCTType
    content::APN
end

struct Monomial <: APN
    type::AbstractPCTType
    base::APN
    power::APN
end

content_fields(::Type{Monomial}) = [:base, :power]
base(n::Monomial) = n.base
power(n::Monomial) = n.power

monomial(base::APN, power::APN) = make_node(Monomial, base, power)

struct Add <: APN
    type::AbstractPCTType
    content::PCTVector
end

function add(args::Vararg{<:APN})
    return make_node(Add, make_node(PCTVector, args...))
end

struct Mul <: APN
    type::AbstractPCTType
    content::PCTVector
end

function mul(args::Vararg{<:APN})
    return make_node(Mul, make_node(PCTVector, args...))
end


abstract type PermInv <: APN end
abstract type Contraction <: PermInv end

function pct_sum(terms::Vararg)
    return make_node(Sum, pct_vec(terms[1:end-1]...), last(terms))
end

mutable struct Sum <: Contraction
    type::AbstractPCTType
    signatures::Vector{AbstractSignatureTree}
    from::PCTVector
    content::APN
    function Sum(type, from::PCTVector, summand::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, Z()) : t for t in content(from)]...)
        signatures = Vector{AbstractSignatureTree}()
        new(type, signatures, from, summand)
    end
end

term_start(n::PermInv) = 3
function signatures!(n::PermInv)
    isempty(n.signatures) || return n.signatures
    from, summand = ff(n), fc(n)
    n.signatures = [SignatureTree(from[i], summand, content(from)[1:end.!=i]) for i in 1:length(from)]
    return n.signatures
end

mutable struct Integral <: Contraction
    type::AbstractPCTType
    signatures::Vector{AbstractSignatureTree}
    from::PCTVector
    content::APN
    function Integral(type, from::PCTVector, integrand::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, R()) : t for t in content(from)]...)
        signatures = Vector{AbstractSignatureTree}()
        new(type, signatures, from, integrand)
    end
end

function pct_int(terms::Vararg)
    return make_node(Integral, pct_vec(terms[1:end-1]...), last(terms))
end


mutable struct Prod <: PermInv
    type::AbstractPCTType
    signatures::Vector{AbstractSignatureTree}
    from::PCTVector
    content::APN
    function Prod(type, from::PCTVector, productant::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, Z()) : t for t in content(from)]...)
        signatures = Vector{AbstractSignatureTree}()
        new(type, signatures, from, productant)
    end
end

function pct_product(terms::Vararg)
    return make_node(Prod, pct_vec(terms[1:end-1]...), last(terms))
end

abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

content_fields(::Type{T}) where {T<:AbstractDelta} = [:upper, :lower, :content]
fc(d::AbstractDelta) = d.content

struct Delta <: AbstractDelta
    type::AbstractPCTType
    upper::APN
    lower::APN
    content::APN
end

function delta(upper_lower::Vararg{APN})
    upper_lower = collect(upper_lower)
    content = last(upper_lower)
    upper_lower = upper_lower[1:end-1]
    n = length(upper_lower)
    content = make_node(Delta, upper_lower[1], upper_lower[n÷2+1], content)
    if n > 2
        return delta(upper_lower[2:n÷2]..., upper_lower[n÷2+2:end]..., content)
    else
        return content
    end
end

struct DeltaNot <: AbstractDelta
    type::AbstractPCTType
    upper::APN
    lower::APN
    content::APN
end


function delta_not(upper_lower::Vararg{APN})
    upper_lower = collect(upper_lower)
    content = last(upper_lower)
    upper_lower = upper_lower[1:end-1]
    n = length(upper_lower)
    content = make_node(DeltaNot, upper_lower[1], upper_lower[n÷2+1], content)
    if n > 2
        return delta_not(upper_lower[2:n÷2]..., upper_lower[n÷2+2:end]..., content)
    else
        return content
    end
end

struct Constant <: TerminalNode
    type::AbstractPCTType
    content::Number
end

constant(n::Number) = make_node(Constant, n)

is_zero(t) = isa(t, Constant) && fc(t) == 0
is_one(t) = isa(t, Constant) && fc(t) == 1
is_minus_one(t) = isa(t, Constant) && fc(t) == -1

struct Let <: APN
    type::AbstractPCTType
    from::PCTVector
    args::PCTVector
    content::APN
end

args(l::Let) = l.args
function pct_let(terms::Vararg{APN})
    terms = collect(terms)
    make_node(Let, pct_vec(terms[1:end÷2]...), pct_vec(terms[end÷2+1:end-1]...), terms[end])
end


struct Negate <: APN
    type::AbstractPCTType
    content::APN
end

function call(vec::PCTVector, c::Constant)
    return content(vec)[fc(c)]
end


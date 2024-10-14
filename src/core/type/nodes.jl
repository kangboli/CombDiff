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
    Negate,
    get_body,
    minfty,
    infty,
    nabla,
    composite,
    rev_composite,
    Composition,
    RevComposition,
    pct_exp,
    pct_log, 
    pct_let,
    Indicator,
    indicator,
    VacExp,
    vac_exp,
    subtract,
    pct_copy,
    domain_indicator,
    int_div

abstract type TerminalNode <: APN end

get_bound(n::T) where {T<:APN} = n.bound
get_body(n::T) where {T<:APN} = n.body

struct PCTVector <: APN
    type::VecType
    content::Vector
    function PCTVector(type::VecType, content::Vararg)
        new(type, collect(content))
    end
end

content(v::PCTVector) = v.content
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


function Base.iterate(v::PCTVector)
    isempty(content(v)) && return nothing
    return content(v)[1], 2
end

function Base.iterate(v::VecType)
    isempty(get_content_type(v)) && return nothing
    return get_content_type(v)[1], 2
end

function Base.iterate(v::PCTVector, state::Int)
    state > length(v) && return nothing
    return content(v)[state], state + 1
end

function Base.iterate(v::VecType, state::Int)
    state > length(v) && return nothing
    return get_content_type(v)[state], state + 1
end

function set_i(v::PCTVector, i::Integer, new_item::APN)
    replace_item(j::Integer) = i == j ? new_item : v[j]
    set_content(v, replace_item.(1:length(v))...)
end

remove_i(v::PCTVector, i::Integer) = pct_vec(content(v)[1:end.!=i]...)

Base.isempty(v::PCTVector) = isempty(content(v))
terms(v::PCTVector) = content(v)

mutable struct Var{T<:AbstractPCTType} <: TerminalNode
    type::T
    range::PCTVector
    body::Symbol
end

name(v::Var) = v.body
range(v::Var) = v.range
var(s::Symbol, type=UndeterminedPCTType()) = make_node(Var, pct_vec(), s; type=type)
var(range::PCTVector, s::Symbol, type=UndeterminedPCTType()) = make_node(Var, range, s; type=type)
infty() = var(:∞, R())
# nabla maps one input to one output. 
# for now we only need to know of the number of input/output, but 
# we need to figure out the actual (parametric) type at some point.
nabla() = var(:∇, MapType(VecType([UndeterminedPCTType()]), VecType([UndeterminedPCTType()]), Dict(:linear=>true)))

_MINFTY=nothing
minfty() = if _MINFTY === nothing 
    global _MINFTY = mul(constant(-1), infty())
else
    _MINFTY
end

struct Conjugate <: APN
    type::AbstractPCTType
    body::APN
end

conjugate(term::APN) = make_node(Conjugate, term)

abstract type AbstractMap <: APN end

struct Map <: AbstractMap
    type::AbstractPCTType
    bound::PCTVector
    body::APN
end

function pct_map(terms::Vararg{APN})
    terms = collect(terms)
    make_node(Map, pct_vec(terms[1:end-1]...), last(terms))
end

function is_univariate(m::AbstractMap)
    params = get_bound(m)
    length(params) == 1 &&
        isa(get_type(first(content(params))), ElementType)
end

abstract type AbstractPullback <: AbstractMap end

struct Pullback <: AbstractPullback
    type::AbstractPCTType
    body::AbstractMap
end

pullback(map::Map) = make_node(Pullback, map)

struct PrimitivePullback <: AbstractPullback
    type::AbstractPCTType
    body::APN
end

pullback(map::Union{Var,PCTVector}) = make_node(PrimitivePullback, map)
# TODO: Figure out the right pattern for a map to be a primitive one instead of 
# asuuming that the caller knows it.
primitive_pullback(n::APN) = make_node(PrimitivePullback, n)

abstract type AbstractCall <: APN end

mapp(c::AbstractCall) = c.mapp
args(c::AbstractCall) = c.args

content_fields(::Type{T}) where {T<:AbstractCall} = [:mapp, :args]

struct Add <: APN
    type::AbstractPCTType
    body::PCTVector
end

struct Call <: AbstractCall
    type::AbstractPCTType
    mapp::APN
    args::PCTVector
end

function call(mapp::APN, args::Vararg)
    make_node(Call, mapp, pct_vec(args...))
end

struct PrimitiveCall <: AbstractCall
    type::AbstractPCTType
    mapp::APN
    args::PCTVector
end

abstract type Univariate <: APN end

struct Exp <: Univariate
    type::AbstractPCTType
    body::APN
end

pct_exp(body::APN) = make_node(Exp, body)

struct Log <: Univariate
    type::AbstractPCTType
    body::APN
end

pct_log(body::APN) = make_node(Log, body)

struct Monomial <: APN
    type::AbstractPCTType
    base::APN
    power::APN
end

content_fields(::Type{Monomial}) = [:base, :power]
base(n::Monomial) = n.base
power(n::Monomial) = n.power

monomial(base::APN, power::APN) = make_node(Monomial, base, power)

function add(args::Vararg)
    return make_node(Add, make_node(PCTVector, args...))
end

struct Mul <: APN
    type::AbstractPCTType
    body::PCTVector
end

function mul(args::Vararg)
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
    bound::PCTVector
    body::APN
    function Sum(type, bound::PCTVector, summand::APN)
        bound = set_content(bound, [get_type(t) == UndeterminedPCTType() ? set_type(t, N()) : t for t in content(bound)]...)
        signatures = Vector{AbstractSignatureTree}()
        new(type, signatures, bound, summand)
    end
end

term_start(n::PermInv) = 3
function signatures!(n::PermInv)
    isempty(n.signatures) || return n.signatures
    bound_var, summand = get_bound(n), get_body(n)
    n.signatures = [SignatureTree(bound_var[i], summand, content(bound_var)[1:end.!=i]) for i in 1:length(bound_var)]
    return n.signatures
end

mutable struct Integral <: Contraction
    type::AbstractPCTType
    signatures::Vector{AbstractSignatureTree}
    bound::PCTVector
    body::APN
    function Integral(type, bound::PCTVector, integrand::APN)
        bound = set_content(bound, [get_type(t) == UndeterminedPCTType() ? set_type(t, R()) : t for t in content(bound)]...)
        signatures = Vector{AbstractSignatureTree}()
        new(type, signatures, bound, integrand)
    end
end

function pct_int(terms::Vararg)
    return make_node(Integral, pct_vec(terms[1:end-1]...), last(terms))
end


mutable struct Prod <: PermInv
    type::AbstractPCTType
    signatures::Vector{AbstractSignatureTree}
    bound::PCTVector
    body::APN
    function Prod(type, bound::PCTVector, productant::APN)
        bound = set_content(bound, [get_type(t) == UndeterminedPCTType() ? set_type(t, N()) : t for t in content(bound)]...)
        signatures = Vector{AbstractSignatureTree}()
        new(type, signatures, bound, productant)
    end
end

function pct_product(terms::Vararg)
    return make_node(Prod, pct_vec(terms[1:end-1]...), last(terms))
end

"""
AbstractDelta should have the field `upper` and `lower` in addition to `body`.
This is counterinuitive for the indicator functions, where the smaller number 
is written on the left. The order was decided for no reason when implementing 
Delta, and Indicator is stuck with the same convention.
"""
abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

content_fields(::Type{T}) where {T<:AbstractDelta} = [:upper, :lower, :body]

struct Delta <: AbstractDelta
    type::AbstractPCTType
    upper::APN
    lower::APN
    body::APN
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
    body::APN
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
    body::Number
end

constant(n::Number) = make_node(Constant, n)

is_zero(t) = isa(t, Constant) && get_body(t) == 0
is_one(t) = isa(t, Constant) && get_body(t) == 1
is_minus_one(t) = isa(t, Constant) && get_body(t) == -1

struct Let <: APN
    type::AbstractPCTType
    bound::PCTVector
    args::PCTVector
    body::APN
end

args(l::Let) = l.args
function pct_let(terms::Vararg{APN})
    terms = collect(terms)
    make_node(Let, pct_vec(terms[1:end÷2]...), pct_vec(terms[end÷2+1:end-1]...), terms[end])
end

content_fields(::Type{Let}) = [:bound, :args, :body]


struct Negate <: APN
    type::AbstractPCTType
    body::APN
end

function call(vec::PCTVector, c::Constant)
    return content(vec)[get_body(c)]
end

abstract type AbstractComp <: APN end

struct Composition <: AbstractComp
    type::AbstractPCTType
    body::PCTVector
end

"""
The same thing as Composition. The only difference is how it is printed.
"""

struct RevComposition <: AbstractComp 
    type::AbstractPCTType
    body::PCTVector
end

function composite(funcs::Vararg)
    make_node(Composition, pct_vec(funcs...))
end

function rev_composite(funcs::Vararg)
    make_node(RevComposition, pct_vec(funcs...))
end


function conjugate(n::PrimitiveCall)
    return make_node(Conjugate, n)
end

function primitive_call(mapp::APN, args::Vararg)
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end

abstract type FieldOperators <: TerminalNode end


function call(mapp::Union{Conjugate,Var,PrimitivePullback,PrimitiveCall, FieldOperators}, args::Vararg)
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end

struct Copy  <: Univariate
    type::AbstractPCTType
    body::Var
end

function pct_copy(body::Var)
    make_node(Copy, body)
end

name(c::Copy) = name(get_body(c))

"""
The indicator function is inclusive (the test is lower <= upper)
"""
struct Indicator <: AbstractDelta
    type::AbstractPCTType
    upper::APN
    lower::APN
    body::APN
end


function make_delta(::Type{T}, upper_lower::Vararg{APN}) where T <: AbstractDelta
    upper_lower = collect(upper_lower)
    content = last(upper_lower)
    upper_lower = upper_lower[1:end-1]
    n = length(upper_lower)
    content = make_node(T, upper_lower[1], upper_lower[n÷2+1], content)
    if n > 2
        return make_delta(T, upper_lower[2:n÷2]..., upper_lower[n÷2+2:end]..., content)
    else
        return content
    end
end

function indicator(upper_lower::Vararg{APN}) 
    make_delta(Indicator, upper_lower...)
end

function domain_indicator(i::Var, d::Domain, c::APN)
    indicator(upper(d), i, indicator(i, lower(d), c))
end

struct VacExp <: APN
    type::AbstractPCTType
    body::APN
end
vac_exp(body::APN) = make_node(VacExp, body)

struct FermiScalar <: APN
    type::AbstractPCTType
    body::APN
end

function fermi_scalar(body)
    return make_node(FermiScalar, body)
end

is_field_op(::FermiScalar) = true

function subtract(a::APN, b::APN)
    return add(a, mul(constant(-1), b))
end

struct IntDiv <: APN
    type::AbstractPCTType
    nom::APN
    denom::APN
end

content_fields(::Type{IntDiv}) = [:nom, :denom]

int_div(nom, denom) = make_node(IntDiv, nom, denom)

get_nom(n::IntDiv) = n.nom
get_denom(n::IntDiv) = n.denom


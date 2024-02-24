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
    composite,
    Composition,
    pct_exp,
    pct_log,
    pct_let,
    pct_copy

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
infty() = var(:∞)
minfty() = mul(constant(-1), infty())

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
    length(terms) == 1 && error("map with no argument is not allowed")
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
    #= if isa(mapp, Map) && length(get_bound(mapp)) != length(args)
        println(pretty(mapp))
        println.(pretty.(args))
        get_body(first(args)) != :t && error("ahah")
        #= length(get_bound(mapp)) == 3 && error("Aha") =#
    end =#
    arg_vec = pct_vec(args...)
    make_node(Call, mapp, arg_vec)
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

abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

content_fields(::Type{T}) where {T<:AbstractDelta} = [:upper, :lower, :body]
fc(d::AbstractDelta) = d.body

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

struct Copy <: Univariate
    type::AbstractPCTType
    body::Var
end

function pct_copy(body::Var)
    make_node(Copy, body)
end

name(c::Copy) = name(get_body(c))

struct Let <: APN
    type::AbstractPCTType
    bound::PCTVector
    args::PCTVector
    body::APN
end

args(l::Let) = l.args
function pct_let(terms::Vararg{APN})
    terms = collect(terms)
    bounds = pct_vec(terms[1:end÷2]...)
    args = pct_vec(terms[end÷2+1:end-1]...)
    body = terms[end]
    make_node(Let, bounds, args, body)
end

content_fields(::Type{Let}) = [:bound, :args, :body]
function Base.iterate(n::Let)
    isa(get_body(n), PCTVector) || error("iterating a let that does not return a vector")
    return n, 1
end
function Base.iterate(::Let, state::Int)
    return nothing
end
#= Base.length(n::Let) = length(get_body(n)) =#


struct Negate <: APN
    type::AbstractPCTType
    body::APN
end

function call(vec::PCTVector, c::Constant)
    return content(vec)[get_body(c)]
end

struct Omega <: APN
    type::AbstractPCTType
    bound::PCTVector
    body::APN
    function Omega(type, bound::PCTVector, summand::APN)
        bound = set_content(bound, [get_type(t) == UndeterminedPCTType() ? set_type(t, N()) : t for t in content(bound)]...)
        new(type, bound, summand)
    end
end

function pct_omega(terms::Vararg)
    return make_node(Omega, pct_vec(terms[1:end-1]...), last(terms))
end

struct Composition <: APN
    type::AbstractPCTType
    body::PCTVector
end

function composite(funcs::Vararg)
    make_node(Composition, pct_vec(funcs...))
end

abstract type FermionicField <: AbstractMap end

struct FermionicFieldCreation <: FermionicField
    type::AbstractPCTType
    body::Symbol
end

struct FermionicFieldAnnihilation <: FermionicField
    type::AbstractPCTType
    body::Symbol
end

struct FermiVacuumType <: AbstractPCTType end
struct FermiVacuum <: APN end

conjugate(n::FermionicFieldCreation) = f_annihilation(get_body(n))
conjugate(n::FermionicFieldAnnihilation) = f_creation(get_body(n))

function conjugate(n::PrimitiveCall)
    fermi_field = mapp(n)
    if isa(fermi_field, FermionicFieldCreation)
        return call(f_annihilation(get_body(fermi_field)), args(n)...)
    elseif isa(fermi_field, FermionicFieldAnnihilation)
        return call(f_creation(get_body(fermi_field)), args(n)...)
    else
        return make_node(Conjugate, n)
    end
end

function call(mapp::Union{Conjugate,Var,PrimitivePullback,PrimitiveCall,FermionicField}, args::Vararg)
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end

struct Indicator <: APN
    type::AbstractPCTType
    index::APN
    lower::APN
    upper::APN
    body::APN
end

function indicator(index::APN, lower::APN, upper::APN, body::APN)
    return make_node(Indicator, index, lower, upper, body)
end

content_fields(::Type{Indicator}) = [:index, :lower, :upper, :body]

get_index(t::Indicator) = t.index
lower(t::Indicator) = t.lower
upper(t::Indicator) = t.upper


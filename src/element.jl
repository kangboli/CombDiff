export Var,
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
    Let,
    Conjugate,
    Mul,
    Pullback,
    PrimitivePullback,
    Constant,
    Add,
    PCTVector,
    Negate,
    make_node,
    content,
    set_content,
    fc,
    terms,
    set_terms,
    from,
    set_from,
    ff,
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
    APN

"""
The root of the AST. Serves as the default parent node.
"""
struct Origin <: APN end

"""
    make_node(T, terms...,
                type=UndeterminedPCTType(),
                meta=Dict())

This function is the gate way for creating all nodes.
The purpose is to ensure at construction that
1. the node is typed (through inference).
2. the node is canonical within its e-class.

"""
function make_node(::Type{T}, terms::Vararg;
    type=UndeterminedPCTType(),
    meta=Dict{Symbol,APN}()
) where {T<:APN}

    S, terms, t = e_class_reduction(T, terms...)
    #= type == UndeterminedPCTType() && (type = partial_inference(S, terms...)) =#
    type == UndeterminedPCTType() && (type = t)
    node = S(type, meta, terms...)
    return node
end

"""
    e_class_reduction(T, terms)

Reduce a term to one of the canonical ones within is e-class.
"""
function e_class_reduction(::Type{T}, terms::Vararg) where {T<:APN}
    return T, collect(terms), partial_inference(T, terms...)
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
    return make_node(T, terms(n)..., type=new_type, meta=meta(n))
end

"""
    terms(n)

Get the subterms of `n`.
"""
terms(n::T) where {T<:APN} = map(f -> getfield(n, f), fieldnames(T)[3:end])

"""
    set_terms(n)

Set the subterms of `n`.
"""
function set_terms(n::T, new_terms...) where {T<:APN}
    make_node(T, new_terms...; type=get_type(n), meta=meta(n))
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

"""
    ff(n)

Get the first field that is considered from.
"""
ff(n::APN) = first(from(n))

content(n::T) where {T<:APN} = map(f -> getfield(n, f), filter(f -> hasfield(T, f), content_fields(T)))

"""
    fc(n)

Get the first field that is considered content.
"""
fc(n::APN) = first(content(n))

function set_pct_fields(n::T, fields::Vector{Symbol}, values...) where {T<:APN}
    isempty(values) && return n
    d = Dict(zip(fields, [values...]))
    take_field(f::Symbol) = get(d, f, getfield(n, f))
    return set_terms(n, take_field.(fieldnames(T)[3:end])...)
end

function set_content(n::T, new_content...) where {T<:APN}
    set_pct_fields(n, content_fields(T), new_content...)
end

function set_from(n::T, new_from...) where {T<:APN}
    set_pct_fields(n, from_fields(T), new_from...)
end

meta(n::APN) = n.meta
base(n::APN) = n
power(::APN) = make_node(Constant, 1)

abstract type TerminalNode <: APN end

mutable struct Var <: TerminalNode
    type::AbstractPCTType
    meta::Dict
    content::Symbol
end

name(v::Var) = v.content
var(s::Symbol, type=UndeterminedPCTType()) = make_node(Var, s; type=type)

struct PCTVector <: APN
    type::AbstractPCTType
    meta::Dict
    content::Vector
    function PCTVector(type::AbstractPCTType, meta::Dict, content::Vararg)
        new(type, meta, [content...])
    end
end

pct_vec(content::Vararg{APN}) = make_node(PCTVector, content...)

function Base.map(f::Function, v::PCTVector)
    make_node(PCTVector, map(f, content(v))...; type=get_type(v), meta=meta(v))
end
Base.setindex(v::PCTVector, indices::Any) = set_content(v, content(v)[indices]...)
Base.getindex(v::PCTVector, indices::Integer) = content(v)[indices]
Base.getindex(v::PCTVector, indices::Any) = make_node(PCTVector, content(v)[indices]...)
Base.first(v::PCTVector) = first(content(v))
Base.last(v::PCTVector) = last(content(v))
Base.length(v::PCTVector) = length(content(v))

function set_i(v::PCTVector, i::Integer, new_item::APN)
    replace_item(j::Integer) = i == j ? new_item : v[j]
    set_content(v, replace_item.(1:length(v))...)
end


function set_content(v::PCTVector, new_content...)
    return make_node(PCTVector, new_content...; type=get_type(v), meta=meta(v))
end

function set_terms(v::PCTVector, new_terms...)
    return set_content(v, new_terms...)
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
    meta::Dict
    content::AbstractMap
end

pullback(map::Map) = make_node(Pullback, map)

struct PrimitivePullback <: AbstractPullback
    type::AbstractPCTType
    meta::Dict
    content::APN
end

pullback(map::Var) = make_node(PrimitivePullback, map)


abstract type AbstractCall <: APN end

mapp(c::AbstractCall) = c.mapp
args(c::AbstractCall) = c.args

content_fields(::Type{T}) where {T<:AbstractCall} = [:mapp, :args]

struct Call <: AbstractCall
    type::AbstractPCTType
    meta::Dict
    mapp::Union{Map,Pullback}
    args::PCTVector
end

function call(mapp::Union{Map,Pullback}, args::Vararg{<:APN})
    make_node(Call, mapp, make_node(PCTVector, args...))
end

struct PrimitiveCall <: AbstractCall
    type::AbstractPCTType
    meta::Dict
    mapp::Union{Var,PrimitivePullback}
    args::PCTVector
end

function call(mapp::Union{Var,PrimitivePullback, PrimitiveCall}, args::Vararg{<:APN})
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end

#= abstract type BuiltinFunction <: APN end

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
end =#

struct Monomial <: APN
    type::AbstractPCTType
    meta::Dict
    base::APN
    power::APN
end

content_fields(::Type{Monomial}) = [:base, :power]
base(n::Monomial) = n.base
power(n::Monomial) = n.power

monomial(base::APN, power::APN) = make_node(Monomial, base, power)

function e_class_reduction(::Type{Monomial}, base::T, power::APN) where T <: APN
    is_zero(base) && return Constant, [0], I()
    is_zero(power) && return Constant, [1], I()
    is_one(power) && return T, terms(base), get_type(base)
    isa(base, Constant) && isa(power, Constant) && return Constant, [fc(base)^fc(power)], partial_inference(Constant, [fc(base)^fc(power)])
    return Monomial, [base, power], partial_inference(Monomial, base, power)
end

struct Add <: APN
    type::AbstractPCTType
    meta::Dict
    content::PCTVector
end

function add(args::Vararg{<:APN})
    return make_node(Add, make_node(PCTVector, args...))
end

#= function make_node(::Type{Add}, term::PCTVector;
    type=partial_inference(Add, term),
    meta=Dict{Symbol,APN}()
    # meta=Dict{Symbol, APN}(:sup_node => Origin())
)

    args = vcat(flatten_add.(content(term))...)
    args = filter(t -> !is_zero(t), args)
    isempty(args) && (args = [make_node(Constant, 0)])
    length(args) == 1 && return first(args)
    #= term = set_content(term, vcat(flatten_mul.(content(term))...)) =#
    return Add(type, meta, make_node(PCTVector, args...))
end =#

function flatten_add(a::Add)
    return vcat(flatten_add.(content(fc(a)))...)
end

flatten_add(a::APN) = [a]

function e_class_reduction(::Type{Add}, term::PCTVector)
    args = vcat(flatten_add.(content(term))...)
    args = filter(t -> !is_zero(t), args)
    isempty(args) && return Constant, [0], I()
    length(args) == 1 && return typeof(first(args)), terms(first(args)), get_type(first(args))
    return Add, [pct_vec(args...)], partial_inference(Add, pct_vec(args...))
end


struct Mul <: APN
    type::AbstractPCTType
    meta::Dict
    content::PCTVector
end

function flatten_mul(a::Mul)
    return vcat(flatten_mul.(content(fc(a)))...)
end

flatten_mul(a::APN) = [a]

function mul(args::Vararg{<:APN})
    return make_node(Mul, make_node(PCTVector, args...))
end

#= function make_node(::Type{Mul}, term::PCTVector;
    type=partial_inference(Mul, term),
    meta=Dict{Symbol,APN}()
    # meta=Dict{Symbol, APN}(:sup_node => Origin())
)

    args = vcat(flatten_mul.(content(term))...)
    args = filter(t -> !is_one(t), args)
    isempty(args) && (args = [make_node(Constant, 1)])
    length(args) == 1 && return first(args)
    return Mul(type, meta, make_node(PCTVector, args...))
end =#

function e_class_reduction(::Type{Mul}, term::PCTVector)
    args = vcat(flatten_mul.(content(term))...)
    args = filter(t -> !is_one(t), args)
    any(is_zero, args) && return Constant, [0], I()
    isempty(args) && return Constant, [1], I()
    if length(args) == 1
        return typeof(first(args)), terms(first(args)), get_type(first(args))
    end
    return Mul, [pct_vec(args...)], partial_inference(Mul, pct_vec(args...))
end

#= function split_constant(m::Mul)
    consts = filter(t -> isa(t, Constant), content(m))
    non_consts = filter(t -> !isa(t, Constant), content(m))
    c = isempty(consts) ? make_node(Constant, 1) : make_node(Constant, prod(content.(consts)))
    n = isempty(non_consts) ? make_node(Constant, 1) : mul(non_consts)Mul
    return c, n
end
 =#
abstract type Contraction <: APN end
#=
function make_node(::Type{T}, terms::Vararg;
    type=partial_inference(T, terms...),
    meta=Dict{Symbol,APN}()
) where {T<:Contraction}
    node = T(type, meta, terms[end-1:end]...)
    length(terms) == 2 && return node
    return make_node(T, terms[1:end-2]..., node)
end =#

function pct_sum(terms::Vararg)
    node = make_node(Sum, terms[end-1:end]...)
    length(terms) == 2 && return node
    return pct_sum(terms[1:end-2]..., node)
end


struct Sum <: Contraction
    type::AbstractPCTType
    meta::Dict
    from::Var
    content::APN
    function Sum(type, meta, from::Var, summand::APN)
        if get_type(from) == UndeterminedPCTType()
            from = set_type(from, I())
        end
        new(type, meta, from, summand)
    end
end

function pct_int(terms::Vararg{APN})
    node = make_node(Integral, terms[end-1:end]...)
    length(terms) == 2 && return node
    return pct_int(terms[1:end-2]..., node)
end

struct Integral <: Contraction
    type::AbstractPCTType
    meta::Dict
    from::Var
    content::APN
    function Integral(type, meta, from::Var, integrand::APN)
        if get_type(from) == UndeterminedPCTType()
            from = set_type(from, R())
        end
        new(type, meta, from, integrand)
    end
end

struct Prod <: APN
    type::AbstractPCTType
    meta::Dict
    from::Var
    content::APN
    function Prod(type, meta, from::Var, productant::APN)
        if get_type(from) == UndeterminedPCTType()
            from = set_type(from, I())
        end
        new(type, meta, from, productant)
    end
end

function pct_product(terms::Vararg{APN}) 
    node = make_node(Prod, terms[end-1:end]...)
    length(terms) == 2 && return node
    return pct_product(terms[1:end-2]..., node)
end

abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

# from_fields(::Type{AbstractDelta}) = [:upper, :lower]
content_fields(::Type{T}) where {T<:AbstractDelta} = [:upper, :lower, :content]
fc(d::AbstractDelta) = d.content

struct Delta <: AbstractDelta
    type::AbstractPCTType
    meta::Dict
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
    meta::Dict
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


struct Conjugate <: APN
    type::AbstractPCTType
    meta::Dict
    content::APN
end

function e_class_reduction(::Type{Conjugate}, term::T) where T <: APN
    t = get_type(term)
    if T == Mul 
        sub_terms = pct_vec(map(conjugate, content(fc(term)))...)
        return Mul, [sub_terms], partial_inference(Mul, sub_terms)
    end
    if T == Constant
        new_const = fc(term)'
        return Constant, [new_const], partial_inference(Constant, new_const)
    end
    T == Conjugate && return typeof(fc(term)), terms(fc(term)), get_type(fc(term))
    t in [I(), R()] && return T, terms(term), get_type(term)
    return Conjugate, [term], get_type(term)
end

conjugate(term::APN) = make_node(Conjugate, term)
    
#=
function make_node(::Type{Conjugate}, term;
    type=get_type(term),
    #= meta=Dict{Symbol, APN}(:sup_node => Origin()) =#
    meta=Dict{Symbol,APN}()
)
    type == I() || type == R() && return term
    node = Conjugate(type, meta, term)
    #= set_sup_node!(term, node) =#
    return node
end =#


struct Constant <: TerminalNode
    type::AbstractPCTType
    meta::Dict
    content::Number
end

constant(n::Number) = make_node(Constant, n)

struct Let <: APN
    type::AbstractPCTType
    meta::Dict
    substitutions::Vector{Pair{Var,<:APN}}
    content::APN
end

substitutions(l::Let) = l.substitutions


struct Negate <: APN
    type::AbstractPCTType
    meta::Dict
    content::APN
end



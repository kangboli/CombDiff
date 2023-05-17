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
    APN,
    pullback


const term_start = 2

"""
    make_node(T, terms...,
                type=UndeterminedPCTType())

This function is the gate way for creating all nodes.
The purpose is to ensure at construction that
1. the node is typed (through inference).
2. the node is canonical within its e-class.

"""
function make_node(::Type{T}, terms::Vararg;
    type=UndeterminedPCTType()
) where {T<:APN}

    S, terms, t = e_class_reduction(T, terms...)
    #= type == UndeterminedPCTType() && (type = partial_inference(S, terms...)) =#
    type == UndeterminedPCTType() && (type = t)
    node = S(type, terms...)
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
    return make_node(T, terms(n)..., type=new_type)
end

"""
    terms(n)

Get the subterms of `n`.
"""
terms(n::T) where {T<:APN} = map(f -> getfield(n, f), fieldnames(T)[term_start:end])

"""
    set_terms(n)

Set the subterms of `n`.
"""
function set_terms(n::T, new_terms...) where {T<:APN}
    make_node(T, new_terms...; type=get_type(n))
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
fc(n::APN)::Union{APN,Number} = first(content(n))

function set_pct_fields(n::T, fields::Vector{Symbol}, values...) where {T<:APN}
    isempty(values) && return n
    d = Dict(zip(fields, [values...]))
    take_field(f::Symbol) = get(d, f, getfield(n, f))
    return set_terms(n, take_field.(fieldnames(T)[term_start:end])...)
end

function set_content(n::T, new_content...) where {T<:APN}
    set_pct_fields(n, content_fields(T), new_content...)
end

function set_from(n::T, new_from...) where {T<:APN}
    set_pct_fields(n, from_fields(T), new_from...)
end

abstract type TerminalNode <: APN end

struct Constant <: TerminalNode
    type::AbstractPCTType
    content::Number
end

constant(n::Number) = make_node(Constant, n)

is_zero(t) = isa(t, Constant) && fc(t) == 0
is_one(t) = isa(t, Constant) && fc(t) == 1
is_minus_one(t) = isa(t, Constant) && fc(t) == -1
base(n::APN) = n
power(::APN) = make_node(Constant, 1)

mutable struct Var{T<:AbstractPCTType} <: TerminalNode
    type::T
    content::Symbol
end

function set_type(n::Var{S}, new_type) where {S<:AbstractPCTType}
    return make_node(Var, terms(n)..., type=new_type)
end

name(v::Var) = v.content
var(s::Symbol, type=UndeterminedPCTType()) = make_node(Var, s; type=type)

struct PCTVector <: APN
    type::VecType
    content::Vector{APN}
    function PCTVector(type::VecType, content::Vararg)
        new(type, [content...])
    end
end

function set_type(n::PCTVector, new_type)
    return make_node(PCTVector, terms(n)..., type=new_type)
end

pct_vec(content::Vararg{APN}) = make_node(PCTVector, content...)

function Base.map(f::Function, v::PCTVector)
    make_node(PCTVector, map(f, content(v))...; type=get_type(v))
end
Base.setindex(v::PCTVector, indices::Any) = set_content(v, content(v)[indices]...)
Base.getindex(v::PCTVector, indices::Integer) = content(v)[indices]
Base.getindex(v::PCTVector, indices::Any) = make_node(PCTVector, content(v)[indices]...)
Base.first(v::PCTVector) = first(content(v))
Base.last(v::PCTVector) = last(content(v))
Base.length(v::PCTVector) = length(content(v))
function Base.append!(v_1::PCTVector, v_2::PCTVector) 
    append!(content(v_1), content(v_2))
    return v_1
end

function set_i(v::PCTVector, i::Integer, new_item::APN)
    replace_item(j::Integer) = i == j ? new_item : v[j]
    set_content(v, replace_item.(1:length(v))...)
end

function remove_i(v::PCTVector, i::Integer)

    new = Vector{APN}()
    for (j, t) in enumerate(content(v))
        j == i && continue
        push!(new, t)
    end

    return pct_vec(new...)
end


function set_content(v::PCTVector, new_content...)
    return make_node(PCTVector, new_content...; type=get_type(v))
end

function set_terms(v::PCTVector, new_terms...)
    return set_content(v, new_terms...)
end

content(v::PCTVector) = v.content
terms(v::PCTVector) = content(v)

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

pullback(map::Var) = make_node(PrimitivePullback, map)


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
    mapp::Union{Var,PrimitivePullback}
    args::PCTVector
end

function call(mapp::Union{Var,PrimitivePullback,PrimitiveCall}, args::Vararg{<:APN})
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end


function apply_symmetry(indices::Vector{Int}, op::Symbol, n::APN)
    return set_content(n, map(t->apply_symmetry(indices, op, t), content(n))...)
end

apply_symmetry(indices::Vector{Int}, op::Symbol, v::PCTVector) = map(t->apply_symmetry(indices, op, t), v)
apply_symmetry(::Vector{Int}, ::Symbol, c::Constant) = c

function apply_symmetry(indices::Vector{Int}, op::Symbol, n::PrimitiveCall)
    new_term = PrimitiveCall(get_type(n), mapp(n), args(n)[collect(indices)])
    op == :conj && return conjugate(new_term)
    op == :neg && return mul(constant(-1), new_term)
    return new_term
end

function dfs(n::APN, syms, sym_graph = Vector{APN}([n]))
    neighbors = Vector{APN}()
    for (indices, op) in syms
        neighbor = apply_symmetry([indices...], op, n)
        neighbor in sym_graph && continue
        push!(neighbors, neighbor)
    end
    append!(sym_graph, neighbors)

    for b in neighbors
        dfs(b, syms, sym_graph)
    end
    return sym_graph
end


function get_call(n::APN)
    ts = terms(n)
    i = findfirst(t->isa(t, PrimitiveCall), ts)
    return ts[i]
end

get_call(n::PrimitiveCall) = n

#= abstract type BuiltinFunction <: APN end

struct Cos <: BuiltinFunction
    type::MapType
    content::APN
end

struct Sin <: BuiltinFunction
    type::MapType
    content::APN
end

struct Exp <: BuiltinFunction
    type::MapType
    content::APN
end =#

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

function flatten_add(a::Add)
    return vcat(flatten_add.(content(fc(a)))...)
end

flatten_add(a::APN) = [a]
fc(a::Add)::PCTVector = a.content


struct Mul <: APN
    type::AbstractPCTType
    content::PCTVector
end

function flatten_mul(a::Mul)
    return vcat(flatten_mul.(content(fc(a)))...)
end

flatten_mul(a::APN) = [a]
fc(a::Mul)::PCTVector = a.content

function mul(args::Vararg{<:APN})
    return make_node(Mul, make_node(PCTVector, args...))
end

function get_call(n::T) where T <: Union{Add, Mul}
    i = findfirst(t->isa(t, PrimitiveCall), content(fc(n)))
    return fc(n)[i]
end


abstract type Contraction <: APN end

function pct_sum(terms::Vararg)
    return make_node(Sum, pct_vec(terms[1:end-1]...), last(terms))
end


struct Sum <: Contraction
    type::AbstractPCTType
    from::PCTVector
    content::APN
    function Sum(type, from::PCTVector, summand::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, I()) : t for t in content(from)]...)
        new(type, from, summand)
    end
end

struct Integral <: Contraction
    type::AbstractPCTType
    from::PCTVector
    content::APN
    function Integral(type, from::PCTVector, integrand::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, R()) : t for t in content(from)]...)
        new(type, from, integrand)
    end
end

function pct_int(terms::Vararg{APN})
    return make_node(Integral, pct_vec(terms[1:end-1]...), last(terms))
end

struct Prod <: APN
    type::AbstractPCTType
    from::PCTVector
    content::APN
    function Prod(type, from::PCTVector, productant::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, I()) : t for t in content(from)]...)
        new(type, from, productant)
    end
end

function pct_product(terms::Vararg{APN})
    return make_node(Prod, pct_vec(terms[1:end-1]...), last(terms))
end


abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

content_fields(::Type{T}) where {T<:AbstractDelta} = [:upper, :lower, :content]
fc(d::AbstractDelta) = d.content

struct Delta <: AbstractDelta
    type::AbstractPCTType
    upper::PCTVector
    lower::PCTVector
    content::APN
end

function delta(upper_lower::Vararg{APN})
    return make_node(Delta, upper_lower...)
end

struct DeltaNot <: AbstractDelta
    type::AbstractPCTType
    upper::PCTVector
    lower::PCTVector
    content::APN
end

function delta_not(upper_lower::Vararg{APN})
    return make_node(DeltaNot, upper_lower...)
end

struct Conjugate <: APN
    type::AbstractPCTType
    content::APN
end

conjugate(term::APN) = make_node(Conjugate, term)

struct Let <: APN
    type::AbstractPCTType
    substitutions::Vector{Pair{Var,<:APN}}
    content::APN
end

substitutions(l::Let) = l.substitutions

struct Negate <: APN
    type::AbstractPCTType
    content::APN
end

#= function delta_parse(upper_lower::Vararg{APN})
    #= length(upper_lower) == 1 && return pct_vec(), pct_vec(), first(upper_lower) =#
    upper_lower = collect(upper_lower)
    content = last(upper_lower)
    upper_lower = upper_lower[1:end-1]
    n = length(upper_lower)
    upper = pct_vec(upper_lower[1:n÷2]...)
    lower = pct_vec(upper_lower[n÷2+1:end]...)
    return upper, lower, content
end =#


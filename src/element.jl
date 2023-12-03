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

base(n::APN) = n
power(::APN) = make_node(Constant, 1)

abstract type TerminalNode <: APN end

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
    content::Vector
    function PCTVector(type::VecType, content::Vararg)
        new(type, [content...])
    end
end

function set_type(n::PCTVector, new_type)
    return make_node(PCTVector, terms(n)..., type=new_type)
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


# function apply_symmetry(indices::Vector{Int}, op::Symbol, n::APN)
#     return set_content(n, map(t->apply_symmetry(indices, op, t), content(n))...)
# end

# function apply_symmetry(indices::Vector{Int}, op::Symbol, n::PrimitiveCall)
#     new_term = PrimitiveCall(get_type(n), mapp(n), args(n)[collect(indices)])
#     op == :conj && return conjugate(new_term)
#     op == :neg && return mul(constant(-1), new_term)
#     return new_term
# end

# function dfs(n::APN, syms, sym_graph = Vector{APN}([n]))
#     neighbors = Vector{APN}()
#     for (indices, op) in syms
#         neighbor = apply_symmetry([indices...], op, n)
#         neighbor in sym_graph && continue
#         push!(neighbors, neighbor)
#     end
#     append!(sym_graph, neighbors)

#     for b in neighbors
#         dfs(b, syms, sym_graph)
#     end
#     return sym_graph
# end

function get_call(n::APN)
    ts = terms(n)
    i = findfirst(t->isa(t, PrimitiveCall), ts)
    return ts[i]
end

get_call(n::PrimitiveCall) = n

function e_class_reduction(::Type{PrimitiveCall}, mapp::Var, args::PCTVector)
    #= if name(mapp) == :A
        println(pretty(args))
    end =#
    get_type(mapp) == UndeterminedPCTType() && return PrimitiveCall, [mapp, args], UndeterminedPCTType()
    # syms = symmetries(get_type(mapp))

    # #= type = partial_inference(PrimitiveCall, mapp, args) =#
    # graph = dfs(PrimitiveCall(UndeterminedPCTType(), mapp, args), syms)
    # #= println(join(pretty.(graph), "\n")) =#
    # result = first(sort(graph, by=get_call))
    return PrimitiveCall, [mapp, args], partial_inference(PrimitiveCall, mapp, args)
end


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

function e_class_reduction(::Type{Monomial}, base::T, power::APN) where {T<:APN}
    is_zero(base) && return Constant, [0], I()
    is_zero(power) && return Constant, [1], I()
    is_one(power) && return T, terms(base), get_type(base)
    isa(base, Constant) && isa(power, Constant) && return Constant, [fc(base)^fc(power)], partial_inference(Constant, [fc(base)^fc(power)])
    return Monomial, [base, power], partial_inference(Monomial, base, power)
end

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

function e_class_reduction(::Type{Add}, term::PCTVector)
    args = vcat(flatten_add.(content(term))...)
    args_const = constant(sum([fc(t) for t in filter(t -> isa(t, Constant), args)], init=0))
    args_rest = filter(t -> !isa(t, Constant), args)
    args = [args_const, args_rest...]
    args = filter(t -> !is_zero(t), args)
    isempty(args) && return Constant, [0], I()
    sort!(args)
    length(args) == 1 && return typeof(first(args)), terms(first(args)), get_type(first(args))
    return Add, [pct_vec(args...)], partial_inference(Add, pct_vec(args...))
end


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

function e_class_reduction(::Type{Mul}, term::PCTVector)
    args = vcat(flatten_mul.(content(term))...)
    args_const = [fc(t) for t in filter(t -> isa(t, Constant), args)]
    args = [constant(prod(args_const, init=1.0)), filter(t -> !isa(t, Constant), args)...]
    args = filter(t -> !is_one(t), args)
    # n_negative = count(is_minus_one, args)
    # args = filter(t -> !is_minus_one(t), args)
    # n_negative % 2 == 1 && pushfirst!(args, constant(-1))
    any(is_zero, args) && return Constant, [0], I()
    isempty(args) && return Constant, [1], I()
    sort!(args)
    if length(args) == 1
        return typeof(first(args)), terms(first(args)), get_type(first(args))
    end
    return Mul, [pct_vec(args...)], partial_inference(Mul, pct_vec(args...))
end

abstract type Contraction <: APN end

function pct_sum(terms::Vararg)
    #= node = make_node(Sum, terms[end-1:end]...)
    length(terms) == 2 && return node
    return pct_sum(terms[1:end-2]..., node) =#
    return make_node(Sum, pct_vec(terms[1:end-1]...), last(terms))
end


struct Sum <: Contraction
    type::AbstractPCTType
    from::PCTVector
    content::APN
    function Sum(type, from::PCTVector, summand::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, I()) : t for t in content(from)]...)
        #= if get_type(content(from)) == UndeterminedPCTType()
            from = set_type(from, I())
        end =#
        new(type, from, summand)
    end
end

function renaming(original::Vector{Var}, n::APN)
    l = length(original)

    tmp_vars = Vector{Var}()
    for (i, t) in zip(1:l, get_type.(original))
        push!(tmp_vars, make_node(Var, Symbol(string("_tmp_", i)); type=t))
    end

    tmp = n
    for (o, d) in zip(original, tmp_vars)
        tmp = subst(tmp, o, d)
    end

    std_vars = Vector{Var}()
    for (s, t) in zip(new_symbol(tmp, num=l), get_type.(tmp_vars))
        push!(std_vars, make_node(Var, s; type=t))
    end

    for (o, d) in zip(tmp_vars, std_vars)
        tmp = subst(tmp, o, d)
    end

    return std_vars, tmp
end

function renaming(original::Vector{Var}, new::Vector{Var}, n::APN)
    l = length(original)

    tmp_vars = Vector{Var}()
    for (i, t) in zip(1:l, get_type.(original))
        push!(tmp_vars, make_node(Var, Symbol(string("_tmp_", i)); type=t))
    end

    tmp = n
    for (o, d) in zip(original, tmp_vars)
        tmp = subst(tmp, o, d)
    end

    n = tmp
    for (o, d) in zip(tmp_vars, new)
        n = subst(n, o, d)
    end

    return n
end



struct Integral <: Contraction
    type::AbstractPCTType
    from::PCTVector
    content::APN
    function Integral(type, from::PCTVector, integrand::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, I()) : t for t in content(from)]...)
        #= if get_type(from) == UndeterminedPCTType()
            from = set_type(from, R())
        end =#
        new(type, from, integrand)
    end
end

function pct_int(terms::Vararg{APN})
    #= node = make_node(Integral, terms[end-1:end]...)
    length(terms) == 2 && return node
    return pct_int(terms[1:end-2]..., node) =#

    return make_node(Integral, pct_vec(terms[1:end-1]...), last(terms))
end

struct Prod <: APN
    type::AbstractPCTType
    from::PCTVector
    content::APN
    function Prod(type, from::PCTVector, productant::APN)
        from = set_content(from, [get_type(t) == UndeterminedPCTType() ? set_type(t, I()) : t for t in content(from)]...)
        #= if get_type(from) == UndeterminedPCTType()
            from = set_type(from, I())
        end =#
        new(type, from, productant)
    end
end

function pct_product(terms::Vararg{APN})
    #= node = make_node(Prod, terms[end-1:end]...)
    length(terms) == 2 && return node
    return pct_product(terms[1:end-2]..., node) =#
    return make_node(Prod, pct_vec(terms[1:end-1]...), last(terms))
end

function e_class_reduction(::Type{T}, from::PCTVector, summand::APN) where T <: Union{Contraction, Prod}

    is_zero(summand) && return Constant, [0], partial_inference(Constant, 0)
    is_one(summand) && T == Prod && return Constant, [1], partial_inference(Constant, 1)
    #= new_from = Vector{Var}()
    for v in variables(summand)
        name(v) in name.(new_from) && continue
        i = findfirst(t->name(t) == name(v), content(from))
        i === nothing && continue
        push!(new_from, from[i])
    end
    new_from, summand = renaming(new_from, summand)
    new_from = pct_vec(new_from...)
    T, [new_from, summand], partial_inference(Sum, new_from, summand) =#
    T, [from, summand], partial_inference(Sum, from, summand)
end



abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

# from_fields(::Type{AbstractDelta}) = [:upper, :lower]
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


struct Conjugate <: APN
    type::AbstractPCTType
    content::APN
end

function e_class_reduction(::Type{Conjugate}, term::T) where {T<:APN}
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
    substitutions::Vector{Pair{Var,<:APN}}
    content::APN
end

substitutions(l::Let) = l.substitutions


struct Negate <: APN
    type::AbstractPCTType
    content::APN
end



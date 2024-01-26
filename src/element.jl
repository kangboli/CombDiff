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
    pullback,
    APN,
    signatures!


term_start(n::APN) = 2

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

    reduced = e_class_reduction(T, terms...)
    S, terms, t = reduced
    #= S, terms, t = e_class_reduction(T, terms...) =#
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

function remake_node(n::T) where T <: APN
    make_node(T, terms(n)...; type=get_type(n))
end

"""
    get_type(n)

Return the PCT type of `n`.
"""
get_type(n::APN)::AbstractPCTType = n.type


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
terms(n::T) where {T<:APN} = map(f -> getfield(n, f), fieldnames(T)[term_start(n):end])

"""
    set_terms(n)

Set the subterms of `n`.
"""
function set_terms(::T, new_terms...) where {T<:APN}
    make_node(T, new_terms...)
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
fc(n::APN)::Union{APN,Number,Symbol} = first(content(n))

function set_pct_fields(n::T, fields::Vector{Symbol}, values...) where {T<:APN}
    isempty(values) && return n
    d = Dict(zip(fields, [values...]))
    take_field(f::Symbol) = get(d, f, getfield(n, f))
    return set_terms(n, take_field.(fieldnames(T)[term_start(n):end])...)
end

function set_content(n::T, new_content...) where {T<:APN}
    set_pct_fields(n, content_fields(T), new_content...)
end

function set_from(n::T, new_from...) where {T<:APN}
    set_pct_fields(n, from_fields(T), new_from...)
end

base(n::APN) = n
power(::APN) = make_node(Constant, 1)

struct PCTVector <: APN
    type::VecType
    content::Vector
    function PCTVector(type::VecType, content::Vararg)
        new(type, [content...])
    end
end

abstract type TerminalNode <: APN end

mutable struct Var{T<:AbstractPCTType} <: TerminalNode
    type::T
    range::PCTVector
    content::Symbol
end

function set_type(n::Var{S}, new_type) where {S<:AbstractPCTType}
    return make_node(Var, terms(n)..., type=new_type)
end

function set_terms(n::T, new_terms...) where {T<:Var}
    make_node(T, new_terms...; type=get_type(n))
end


name(v::Var) = v.content
range(v::Var) = v.range
var(s::Symbol, type=UndeterminedPCTType()) = make_node(Var, pct_vec(), s; type=type)
var(range::PCTVector, s::Symbol, type=UndeterminedPCTType()) = make_node(Var, range, s; type=type)

struct Conjugate <: APN
    type::AbstractPCTType
    content::APN
end

function e_class_reduction(::Type{Conjugate}, term::T) where {T<:APN}
    t = get_type(term)
    t in [Z(), I(), R()] && return T, terms(term), get_type(term)
    if T == Mul
        sub_terms = pct_vec(map(conjugate, content(fc(term)))...)
        return Mul, [sub_terms], partial_inference(Mul, sub_terms)
    end
    if T == Constant
        new_const = fc(term)'
        return Constant, [new_const], partial_inference(Constant, new_const)
    end
    if T <: Contraction
        new_terms = [ff(term), conjugate(fc(term))]
        return T, new_terms, partial_inference(T, new_terms...) 
    end

    if T == Delta
        new_terms = [lower(term), upper(term), conjugate(fc(term))]
        return T, new_terms, partial_inference(T, new_terms...)
    end
    T == Conjugate && return typeof(fc(term)), terms(fc(term)), get_type(fc(term))
    return Conjugate, [term], get_type(term)
end

conjugate(term::APN) = make_node(Conjugate, term)

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

function Base.iterate(v::Union{PCTVector, VecType})
    isempty(content(v)) && return nothing 
    return content(v)[1], 2
end

function Base.iterate(v::Union{PCTVector, VecType}, state::Int)
    state > length(v) && return nothing
    return content(v)[state], state+1
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
Base.isempty(v::PCTVector) = isempty(content(v))
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

pullback(map::Union{Var, PCTVector}) = make_node(PrimitivePullback, map)
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

function call(mapp::Union{Conjugate, Var,PrimitivePullback,PrimitiveCall}, args::Vararg{<:APN})
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end


function get_call(n::APN)
    ts = terms(n)
    i = findfirst(t->isa(t, PrimitiveCall), ts)
    return ts[i]
end

get_call(n::PrimitiveCall) = n

function e_class_reduction(::Type{PrimitiveCall}, mapp::Var, args::PCTVector)
    get_type(mapp) == UndeterminedPCTType() && return PrimitiveCall, [mapp, args], UndeterminedPCTType()
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

function e_class_reduction(::Type{Monomial}, base::T, power::APN) where {T<:APN}
    is_zero(base) && return Constant, [0], I()
    is_zero(power) && return Constant, [1], Z()
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
    new_terms = vcat(flatten_add.(content(term))...)
    const_terms = constant(sum([fc(t) for t in filter(t -> isa(t, Constant), new_terms)], init=0))
    rest_terms = filter(t -> !isa(t, Constant), new_terms)
    new_terms = [const_terms, rest_terms...]
    new_terms = filter(t -> !is_zero(t), new_terms)
    term_dict = Dict{APN, Number}()
    for a in new_terms
        if isa(a, Constant) 
            term_dict[constant(1)] = fc(a) + get(term_dict, constant(1), 0)
            continue
        elseif isa(a, Mul) 
            constant_term = filter(t->isa(t, Constant), content(fc(a)))
            constant_term = isempty(constant_term) ? constant(1) : first(constant_term)
            rest = mul(filter(t->!isa(t, Constant), content(fc(a)))...)
            term_dict[rest] = fc(constant_term) + get(term_dict, rest, 0)
        else
            term_dict[a] = 1 + get(term_dict, a, 0)
        end
    end

    new_terms = [v == 1 ? k : mul(constant(v), k) for (k, v) in term_dict if v != 0]

    if count(a->isa(a, Map), new_terms) > 1
        map_dict = Dict{Int, Vector{APN}}()
        remaining_terms = Vector{APN}()
        for a in new_terms
            if isa(a, Map) 
                map_dict[length(ff(a))] = push!(get(map_dict, length(ff(a)), []), a)
            else
                push!(remaining_terms, a)
            end
        end
        function process_kv(k, v)
            have_common_names = all(i->name.(ff(v[i]))==name.(ff(v[1])), 1:length(v))
            new_from = have_common_names ? ff(v[1]) : 
            pct_vec(map(var, new_symbol(v...; num=length(ff(v[1])), symbol=:_a), get_type.(ff(v[1])))...)

            return pct_map(new_from..., add([ecall(x, new_from...) for x in v]...))
        end

        new_maps = [process_kv(k, v) for (k, v) in map_dict]
        new_terms = [remaining_terms..., new_maps...]
    end

    sort!(new_terms)
    length(new_terms) == 0 && return Constant, [0], I()
    length(new_terms) == 1 && return typeof(first(new_terms)), terms(first(new_terms)), get_type(first(new_terms))

    return Add, [pct_vec(new_terms...)], partial_inference(Add, pct_vec(new_terms...)) 

    #= map_terms = filter(t->isa(t, Map), new_terms)
    nonmap_terms = filter(t->!isa(t, Map), new_terms)
    length(map_terms) <= 1 && return Add, [pct_vec(new_terms...)], partial_inference(Add, pct_vec(new_terms...))
    m = first(map_terms)
    #= if all(t->ff(t) == ff(m), map_terms[2:end])
        new_from = ff(m)
    else
    end =#
    new_from = pct_vec(map(var, new_symbol(term; num=length(ff(m)), symbol=:_a), get_type.(ff(m)))...)
    new_map = pct_map(new_from..., add(map(t->ecall(t, new_from...), map_terms)...))
    return Add, [nonmap_terms..., new_map], partial_inference(Add, pct_vec(nonmap_terms..., new_map)) =#
    
    #= if any(t->isa(t, MapType), get_type.(new_terms))
        # allequal(get_type.(new_terms)) || error("adding tensors of different types")
        m = first(new_terms)
        #= if all(t->ff(t) == ff(m), new_terms[2:end])
            new_from = ff(m)
        else
        end =#
        new_from = pct_vec(map(var, new_symbol(term; num=length(ff(m)), symbol=:_a), get_type.(ff(m)))...)
        new_terms = [new_from, add(map(t->ecall(t, new_from...), new_terms)...)]
        return Map, new_terms, partial_inference(Map, new_terms...)
    end

    return Add, [pct_vec(new_terms...)], partial_inference(Add, pct_vec(new_terms...)) =#
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
    any(is_zero, args) && return Constant, [0], I()
    isempty(args) && return Constant, [1], Z()
    sort!(args)
    if length(args) == 1
        return typeof(first(args)), terms(first(args)), get_type(first(args))
    end
    return Mul, [pct_vec(args...)], partial_inference(Mul, pct_vec(args...))
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
    n.signatures = [SignatureTree(from[i], summand, content(from)[1:end .!= i]) for i in 1:length(from)]
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

function e_class_reduction(::Type{T}, from::PCTVector, summand::S) where {T <: Contraction, S<:APN}

    is_zero(summand) && return Constant, [0], partial_inference(Constant, 0)
    # TODO: Rewrite this with multiple dispatch
    # is_one(summand) && T == Prod && return Constant, [1], partial_inference(Constant, 1)
    isempty(content(from)) && return S, terms(summand), get_type(summand)
    if T == S 
        new_from = pct_vec(content(from)..., content(ff(summand))...)
        return T, [new_from, fc(summand)], partial_inference(Sum, new_from, fc(summand))
    end

    if isa(summand, Map)
        #= i = findfirst(t -> startswith(string(name(t)), "_"), content(ff(summand)))
        j = findfirst(t -> !startswith(string(name(t)), "_"), content(from)) =#
        fcsummand, ffsummand = fc(summand), ff(summand)
        #= if i !== nothing && j !== nothing
            tmp = var(first(new_symbol(from..., summand, num=1))) 
            tmp_fcsummand = subst(fc(summand), ff(summand)[i], tmp)
            tmp_fcsummand = subst(tmp_fcsummand, from[i], ff(summand)[i])
            fcsummand = subst(tmp_fcsummand, tmp, from[i])
            ffsummand = pct_vec(content(ff(summand))[1:end .!= i]...)
            from = pct_vec(content(from)[1:end .!= i]..., ff(summand)[i])
            new_sum = pct_sum(from..., fcsummand)
            return Map, [from[i], ]
        end
 =#
        new_sum = pct_sum(from..., fcsummand)
        return Map, [ffsummand, new_sum], partial_inference(Map, ffsummand, new_sum)
        #= new_from = pct_vec(from..., ff(summand)...)
        return T, [new_from, fc(summand)], partial_inference(T, new_from, fc(summand)) =#
    end

    T, [from, summand], partial_inference(Sum, from, summand)
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

function call(vec::PCTVector, c::Constant)
    return content(vec)[fc(c)]
end

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

symmetric(d::Domain) = haskey(d.meta, :symmetric) && d.meta[:symmetric]
symmetric(::ElementType) = false
#= symmetric(v::Var) = symmetric(get_type(v)) || add(range(v)...) == constant(0) =#
symmetric(v::Var) = symmetric(get_type(v)) 

is_periodic(d::Domain) = haskey(d.meta, :periodic) && d.meta[:periodic]
is_periodic(::ElementType) = false

is_contractable(d::Domain) = !haskey(d.meta, :contractable) || d.meta[:contractable]
is_contractable(::ElementType) = true
#= is_contractable(v::Var) = is_contractable(get_type(v)) && isempty(range(v)) =#
is_contractable(v::Var) = is_contractable(get_type(v))


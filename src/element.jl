export Var, Map, AbstractCall, PrimitiveCall, Sum, Prod, Call, Let, Delta, make_node!, Conjugate, Mul, Pullback, Constant, Add, terms, set_content!, set_terms!, PCTVector, fc, ff, Negate, mul, add, get_type, mapp, args, name, content, from


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
                    meta=Dict{Symbol, APN}()
                    # meta=Dict{Symbol, APN}(:sup_node => Origin())
                    ) where {T<:APN}
    node = T(type, meta, terms...)
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
function set_terms!(n::T, new_terms...) where {T<:APN}
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

function set_pct_fields!(n::T, fields::Vector{Symbol}, values...) where {T<:APN}
    isempty(values) && return n
    d = Dict(zip(fields, [values...]))
    take_field(f::Symbol) = get(d, f, getfield(n, f))
    return set_terms!(n, take_field.(fieldnames(T)[3:end])...)
end

function set_content!(n::T, new_content...) where {T<:APN}
    set_pct_fields!(n, content_fields(T), new_content...)
end

function set_from!(n::T, new_from...) where {T<:APN}
    set_pct_fields!(n, from_fields(T), new_from...)
end

meta(n::APN) = n.meta
base(n::APN) = n
power(::APN) = make_node!(Constant, 1)

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
Base.setindex(v::PCTVector, indices::Any) = set_content!(v, content(v)[indices]...)
Base.getindex(v::PCTVector, indices::Integer) = content(v)[indices]
Base.getindex(v::PCTVector, indices::Any) = make_node!(PCTVector, content(v)[indices]...)
Base.first(v::PCTVector) = first(content(v))
Base.last(v::PCTVector) = last(content(v))
Base.length(v::PCTVector) = length(content(v))

function set_i(v::PCTVector, i::Integer, new_item::APN)
    replace_item(j::Integer) = i == j ? new_item : v[j]
    set_content!(v, replace_item.(1:length(v))...)
end


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

struct Pullback <: AbstractPullback
    type::AbstractPCTType
    meta::Dict
    content::AbstractMap
end

pullback(map::Map) = make_node!(Pullback, map)

struct PrimitivePullback <: AbstractPullback
    type::AbstractPCTType
    meta::Dict
    content::Union{Var, PrimitivePullback}
end

pullback(map::Var) = make_node!(PrimitivePullback, map)


abstract type AbstractCall <: APN end

mapp(c::AbstractCall) = c.mapp
args(c::AbstractCall) = c.args

content_fields(::Type{T}) where T <: AbstractCall = [:mapp, :args]

struct Call <: AbstractCall
    type::AbstractPCTType
    meta::Dict
    mapp::Union{Map, Pullback}
    args::PCTVector
end

function call(mapp::Union{Map, Pullback}, args::Vararg{<:APN})
    make_node!(Call, mapp, make_node!(PCTVector, args...))    
end

struct PrimitiveCall <: AbstractCall
    type::AbstractPCTType
    meta::Dict
    mapp::Union{Var, PrimitivePullback}
    args::PCTVector
end

function call(mapp::Union{Var, PrimitivePullback}, args::Vararg{<:APN})
    make_node!(PrimitiveCall, mapp, make_node!(PCTVector, args...)) 
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
base(n::Monomial) = n.base
power(n::Monomial) = n.power


struct Add <: APN
    type::AbstractPCTType
    meta::Dict
    content::PCTVector
end

function add(args::Vararg{<:APN})
    #= args = vcat(flatten_add.(args)...)
    length(args) == 1 && return first(args) =#
    return make_node!(Add, make_node!(PCTVector, args...))
end

function make_node!(::Type{Add}, term::PCTVector;
                    type=partial_inference(Add, term), 
                    meta=Dict{Symbol, APN}()
                    # meta=Dict{Symbol, APN}(:sup_node => Origin())
                    ) 
    
    args = vcat(flatten_add.(content(term))...)
    args = filter(t->!is_zero(t), args)
    isempty(args) && (args = [make_node!(Constant, 0)])
    length(args) == 1 && return first(args)
    #= term = set_content!(term, vcat(flatten_mul.(content(term))...)) =#
    return Add(type, meta, make_node!(PCTVector, args...))
end

struct Mul <: APN
    type::AbstractPCTType
    meta::Dict
    content::PCTVector
end

function flatten_add(a::Add) 
    return vcat(flatten_add.(content(fc(a)))...)
end

flatten_add(a::APN) = [a]

function flatten_mul(a::Mul) 
    return vcat(flatten_mul.(content(fc(a)))...)
end

flatten_mul(a::APN) = [a]

function mul(args::Vararg{<:APN})
    return make_node!(Mul, make_node!(PCTVector, args...))
end

function make_node!(::Type{Mul}, term::PCTVector;
                    type=partial_inference(Mul, term), 
                    meta=Dict{Symbol, APN}()
                    # meta=Dict{Symbol, APN}(:sup_node => Origin())
                    ) 
    
    args = vcat(flatten_mul.(content(term))...)
    args = filter(t->!is_one(t), args)
    isempty(args) && (args = [make_node!(Constant, 1)])
    length(args) == 1 && return first(args)
    #= term = set_content!(term, vcat(flatten_mul.(content(term))...)) =#
    return Mul(type, meta, make_node!(PCTVector, args...))
end


function split_constant(m::Mul)
    consts = filter(t -> isa(t, Constant), content(m))
    non_consts = filter(t -> !isa(t, Constant), content(m))
    c = isempty(consts) ? make_node!(Constant, 1) : make_node!(Constant, prod(content.(consts)))
    n = isempty(non_consts) ? make_node!(Constant, 1) : mul(non_consts)Mul
    return c, n
end

abstract type Contraction <: APN end

function make_node!(::Type{T}, terms::Vararg;
                    type=partial_inference(T, terms...), 
                    #= meta=Dict{Symbol, APN}(:sup_node => Origin()) =#
                    meta=Dict{Symbol, APN}()
                    ) where {T<:Contraction}
    #= terms = [terms...] =#
    node = T(type, meta, terms[end-1:end]...)
    #= map(t -> set_sup_node!(t, node), terms[end-1:end]) =#
    length(terms) == 2 && return node
           
    return make_node!(T, terms[1:end-2]..., node)

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
end

abstract type AbstractDelta <: APN end

upper(d::AbstractDelta) = d.upper
lower(d::AbstractDelta) = d.lower

# from_fields(::Type{AbstractDelta}) = [:upper, :lower]
content_fields(::Type{T}) where T <: AbstractDelta = [:upper, :lower, :content]
fc(d::AbstractDelta) = d.content

#= function make_node!(::Type{T}, terms::Vararg;
                    type=partial_inference(T, terms...), 
                    #= meta=Dict{Symbol, APN}(:sup_node => Origin()) =#
                    meta=Dict{Symbol, APN}()
                    ) where {T<:AbstractDelta}
    terms = [terms...]
    h = length(terms) ÷ 2
    args = [terms[1], terms[h+1], last(terms)]
    node = T(type, meta, args...)
    #= map(t -> set_sup_node!(t, node), args) =#
    length(terms) == 3 && return node
    return make_node!(T, terms[2:h]..., terms[h+2:end]..., node)
end =#

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
    content = make_node!(Delta, upper_lower[1], upper_lower[n÷2+1], content)
    if n > 2 
        return delta(upper_lower[2:n÷2]...,upper_lower[n÷2+1:end]..., content)
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
    upper_lower = upper_lower[1:-1]
    n = length(upper_lower)
    content = make_node!(DeltaNot, upper_lower[1], upper_lower[n÷2+1], content)
    if n > 2 
        return delta_not(upper_lower[2:n÷2]...,upper_lower[n÷2+1:end], content) 
    else
        return content
    end
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
                    #= meta=Dict{Symbol, APN}(:sup_node => Origin()) =#
                    meta=Dict{Symbol, APN}()
                    )
    type == I() || type == R() && return term
    node = Conjugate(type, meta, term)
    #= set_sup_node!(term, node) =#
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


struct Negate <: APN
    type::AbstractPCTType
    meta::Dict
    content::APN
end



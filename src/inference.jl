export TypeContext, inference, partial_inference

struct TypeContext
    content::Dict{Symbol, Vector{<:AbstractPCTType}}
end

content(context::TypeContext) = context.content

TypeContext() = TypeContext(Dict{Symbol, AbstractPCTType}())

#= inference(f::APN) = inference(f::APN, TypeContext()) =#

Base.haskey(c::TypeContext, k) = haskey(content(c), k)
Base.getindex(c::TypeContext, k) = first(content(c)[k])

function pct_push!(c::TypeContext, key::Symbol, type::AbstractPCTType)
    if haskey(content(c), key) 
        return pushfirst!(content(c)[key], type)
    else
        content(c)[key] = Vector{AbstractPCTType}()
        push!(content(c)[key], type)
    end
end

function pct_pop!(c::TypeContext, key::Symbol, value=nothing)
    popped = popfirst!(content(c)[key])
    value !== nothing && @assert value == popped
    return popped
end

function op_context!(vec::PCTVector, op!::Function, context::TypeContext)

    add_context!(v::Var) = op!(context, name(v), get_type(v)) 
    function add_context!(v::PrimitiveCall) 
        map_type = get_type(mapp(v))
        op!(context, name(mapp(v)), map_type)
        for (a, t) in zip(content(args(v)), content(from(map_type)))
            a.type = t
            op!(context, name(a), t)
        end
    end

    map(add_context!, content(vec))
end

function inference(n::T, context::TypeContext=TypeContext()) where T <: APN
    has_from = any(f->hasfield(T, f), from_fields(T))
    if has_from
        op_context!(ff(n), pct_push!, context)
        n = set_from!(n, map(t->inference(t, context), from(n))...)
    end

    n = set_content!(n, map(t->inference(t, context), content(n))...)
    has_from && op_context!(ff(n), pct_pop!, context)
    return set_type(n, partial_inference(T, terms(n)...))
end

function inference(v::Var, context::TypeContext)
    set_type(v, context[name(v)])
end

inference(c::Constant, ::TypeContext) = set_type(c, partial_inference(Constant, terms(c)...))

function partial_inference(::Type{PCTVector}, terms...)
    return VecType(get_type.([terms...]))
end

function partial_inference(::Type{Map}, terms...)
    from, content = terms
    return MapType(get_type(from), get_type(content))
end

partial_inference(::Type{Var}, ::Symbol) = UndeterminedPCTType()

function partial_inference(::Type{T}, terms...) where T <: AbstractCall
    return content(get_type([terms...][end-1]))
end

function partial_inference(::Type{T}, term) where T <: Union{Add, Mul}
    return escalate(map(get_type, content(term))...)
end


function partial_inference(::Type{T}, terms...)  where T <: Contraction
    return get_type(last(terms))
end

partial_inference(::Type{Conjugate}, terms...) = get_type(last(terms))

function partial_inference(::Type{Pullback}, mapp)
    from_type = from(get_type(mapp))
    content_type = content(get_type(mapp))
    MapType(add_content(from_type, content_type), fc(from_type))
end

function partial_inference(::Type{Constant}, term)
    isa(term, Int) && return I()
    isa(term, Real) && return R()
    isa(term, Complex) && return C()
end

function partial_inference(::Type{T}, terms...) where T <: AbstractDelta
    get_type(last(terms))
end

partial_inference(::Type{Negate}, term) = get_type(term)


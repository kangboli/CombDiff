export TypeContext, inference, partial_inference, pct_push!, pct_pop!

struct TypeContext
    content::Dict{Symbol, Vector{<:AbstractPCTType}}
end

content(context::TypeContext) = context.content

function TypeContext() 
    context = TypeContext(Dict{Symbol, AbstractPCTType}())
    pct_push!(context, :_, UndeterminedPCTType())
    return context
end

#= inference(f::APN) = inference(f::APN, TypeContext()) =#

Base.haskey(c::TypeContext, k) = haskey(content(c), k)
Base.getindex(c::TypeContext, k) = first(content(c)[k])

function pct_push!(c::TypeContext, key::Symbol, type::AbstractPCTType; replace=false)
    if haskey(content(c), key) 
        if replace
            content(c)[key][1] = type
        else
            pushfirst!(content(c)[key], type)
        end
    else
        content(c)[key] = Vector{AbstractPCTType}()
        push!(content(c)[key], type)
    end
    return type
end

function pct_pop!(c::TypeContext, key::Symbol, value=nothing)
    haskey(content(c), key) || error("variable $(key) is undefined.")
    popped = popfirst!(content(c)[key])
    value !== nothing && @assert value == popped
    return popped
end


op_context!(v::Var, op!::Function, context::TypeContext) = op!(context, name(v), get_type(v)) 

function op_context!(v::PrimitiveCall, op!::Function, context::TypeContext) 
    #= map_type = get_type(mapp(v)) =#
    map_type = context[name(mapp(v))]
    #= op!(context, name(mapp(v)), map_type) =#
    for (a, t) in zip(content(args(v)), content(from(map_type)))
        a.type = t
        op!(context, name(a), t)
    end
end

function op_context!(vec::PCTVector, op!::Function, context::TypeContext)
    map(t->op_context!(t, op!, context), content(vec))
end

inference(n::Any) = n

function inference(n::T, context::TypeContext=TypeContext()) where T <: APN
    has_from = any(f->hasfield(T, f), from_fields(T))
    if has_from
        op_context!(ff(n), pct_push!, context)
        n = set_from(n, map(t->inference(t, context), from(n))...)
    end

    n = set_content(n, map(t->inference(t, context), content(n))...)
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
    #= return content(get_type([terms...][end-1])) =#
    return content(get_type(first(terms)))
end

function partial_inference(::Type{T}, term) where T <: Union{Add, Mul}
    return escalate(map(get_type, content(term))...)
end


function partial_inference(::Type{T}, terms...)  where T <: Contraction
    return get_type(last(terms))
end

function partial_inference(::Type{Prod}, terms...)  
    return get_type(last(terms))
end

partial_inference(::Type{Conjugate}, terms...) = get_type(last(terms))

function partial_inference(::Type{Pullback}, mapp)
    from_type = from(get_type(mapp))
    content_type = content(get_type(mapp))
    MapType(add_content(from_type, content_type), fc(from_type))
end

function partial_inference(::Type{PrimitivePullback}, v::Union{Var, Map})
    get_type(v) == UndeterminedPCTType() && return UndeterminedPCTType()
    from_type = from(get_type(v))
    content_type = content(get_type(v))
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

#= partial_inference(::Type{Negate}, term) = get_type(term) =#

partial_inference(::Type{Monomial}, base::APN, power::APN) = escalate(get_type(base), get_type(power))

function inference(d::Domain)
    context = TypeContext()
    vars = vcat(variables(lower(d)), variables(upper(d)))
    for v in vars
        pct_push!(context, name(v), base(d))
    end

    return Domain(base(d), 
           inference(lower(d), context),
           inference(upper(d), context), 
           meta(d))
end



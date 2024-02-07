export TypeContext, inference, partial_inference, pct_push!, pct_pop!

struct TypeContext
    name_to_type::Dict{Symbol,Vector{<:AbstractPCTType}}
    name_to_variable::Dict{Symbol,Vector}
end

get_name_to_type(context::TypeContext) = context.name_to_type
get_name_to_variable(context::TypeContext) = context.name_to_variable

default_context() = TypeContext(
    Dict{Symbol,Vector{<:AbstractPCTType}}(
        :CV => [MapType(VecType([N()]), C())],
        :RV => [MapType(VecType([N()]), R())],
        :CF => [MapType(VecType([C()]), C())],
        :RF => [MapType(VecType([R()]), R())],
        :CM => [MapType(VecType([N(), N()]), C())],
        :RM => [MapType(VecType([N(), N()]), R())],
        :CO => [MapType(VecType([C(), C()]), C())],
        :RO => [MapType(VecType([R(), R()]), R())],
        :CT => [MapType(VecType([N(), N(), N()]), C())],
        :RT => [MapType(VecType([N(), N(), N()]), R())],
        :Her => [MapType(VecType([N(), N()]), C(), Dict(:symmetries => (((2, 1), :conj),),))],
        :Sym => [MapType(VecType([N(), N()]), R(), Dict(:symmetries => (((2, 1), :id),),))],
    ),
    Dict{Symbol,Vector{<:Var}}(
    :Infty => [infty()],
    #= :N => [var(pct_vec(constant(1), infty()), :N, N())] =#
    )
)

function TypeContext()
    context = default_context()
    push_var!(context, :_, var(:_, UndeterminedPCTType()))
    return context
end

Base.haskey(c::TypeContext, k) = haskey(get_name_to_type(c), k)
Base.getindex(c::TypeContext, k) = first(get_name_to_type(c)[k])

function pct_push!(c::TypeContext, key::Symbol, type::AbstractPCTType; replace=false)
    if haskey(get_name_to_type(c), key)
        if replace
            get_name_to_type(c)[key][1] = type
        else
            pushfirst!(get_name_to_type(c)[key], type)
        end
    else
        get_name_to_type(c)[key] = Vector{AbstractPCTType}()
        push!(get_name_to_type(c)[key], type)
    end
    return type
end

function pct_pop!(c::TypeContext, key::Symbol, value=nothing)
    haskey(get_name_to_type(c), key) || error("type $(key) is undefined.")
    popped = popfirst!(get_name_to_type(c)[key])
    value !== nothing && @assert value == popped
    return popped
end

function push_var!(c::TypeContext, key::Symbol, v::Var)
    list = get!(get_name_to_variable(c), key, [])
    push!(list, v)
end

function pop_var!(c::TypeContext, key::Symbol)
    haskey(get_name_to_variable(c), key) || error("variable $(key) is undefined")
    return pop!(get_name_to_variable(c)[key])
end

function get_var(c::TypeContext, key::Symbol)
    haskey(get_name_to_variable(c), key) || error("variable $(key) is undefined")
    return last(get_name_to_variable(c)[key])
end

#= op_context!(v::Var, op!::Function, context::TypeContext) = op!(context, name(v), get_type(v))

function op_context!(vec::PCTVector, op!::Function, context::TypeContext)
    map(t -> op_context!(t, op!, context), content(vec))
end =#

inference(n::Any) = n

function inference(n::T, context::TypeContext=TypeContext()) where T <: APN
    has_bound = any(f->hasfield(T, f), bound_fields(T))
    if has_bound
        #= op_context!(get_bound(n), pct_push!, context) =#
        map(b->push_var!(context, get_body(b), b), content(get_bound(n)))
        # the following line may be redundant.
        n = set_bound(n, map(t->inference(t, context), [get_bound(n)])...)
    end
    n = set_content(n, map(t->inference(t, context), content(n))...)
    has_bound && map(b->pop_var!(context, get_body(b)), content(get_bound(n)))
    # Setting the type may also be redundant.
    return set_type(n, partial_inference(typeof(n), terms(n)...))
end

function inference(v::Var, context::TypeContext)
    startswith(string(get_body(v)), "__") && return v
    set_type(v, get_type(last(get_name_to_variable(context)[name(v)])))
end

function inference(l::Let, context::TypeContext)
    typed_bound, typed_args = [], []
    for (f, a) in zip(get_bound(l), args(l))
        a = inference(a, context)
        f = set_type(f, get_type(a))
        push!(typed_bound, f)
        push!(typed_args, a)
        pct_push!(context, get_body(f), f)
    end
    
    typed_content = inference(get_body(l), context)
    map(f -> pct_pop!(context, get_body(f)), typed_bound)
    return l = pct_let(typed_bound..., typed_args..., typed_content) 
end


inference(c::Constant, ::TypeContext) = set_type(c, partial_inference(Constant, terms(c)...))

function partial_inference(::Type{T}, terms...)::AbstractPCTType where T <: PCTVector
    return VecType(get_type.([terms...]))
end

function partial_inference(::Type{Map}, terms...)::AbstractPCTType
    bound, content = terms
    return MapType(get_type(bound), get_type(content))
end

function partial_inference(::Type{T}, ::PCTVector, ::Symbol)::AbstractPCTType where T <: Var 
    UndeterminedPCTType()
end

function partial_inference(::Type{T}, terms...)::AbstractPCTType where T <: AbstractCall
    mapp = first(terms)
    if startswith(string(get_body(mapp)), "__")
        length(collect(terms)) != 2 && error("control function on more than one argument is not supported")
        return get_type(last(terms))
    end
    return get_body_type(get_type(first(terms)))
end

function partial_inference(::Type{Let}, terms...)::AbstractPCTType
    return get_type(last(terms))
end


function partial_inference(::Type{T}, term::PCTVector)::AbstractPCTType where T <: Union{Add, Mul}
    @assert length(term) > 0
    return escalate(map(get_type, content(term))...)
end


function partial_inference(::Type{T}, terms...)::AbstractPCTType  where T <: Contraction
    return get_type(last(terms))
end

function partial_inference(::Type{Prod}, terms...)::AbstractPCTType  
    return get_type(last(terms))
end

function partial_inference(::Type{Conjugate}, term)::AbstractPCTType 
    isa(get_type(term), ElementType) && return get_type(term)
    return MapType(VecType([get_body_type(get_type(term))]), get_bound_type(get_type(term)), meta(get_type(term)))
end

function partial_inference(::Type{Pullback}, mapp)::AbstractPCTType
    bound_type = get_bound_type(get_type(mapp))
    body_type = get_body_type(get_type(mapp))
    MapType(add_content(bound_type, body_type), first(get_content_type(bound_type)))
end

function partial_inference(::Type{PrimitivePullback}, v::APN)::AbstractPCTType
    get_type(v) == UndeterminedPCTType() && return UndeterminedPCTType()
    bound_type = get_bound_type(get_type(v))
    body_type = get_body_type(get_type(v))
    MapType(add_content(bound_type, body_type), first(get_content_type(bound_type)))
end

function partial_inference(::Type{PrimitivePullback}, v::PCTVector)::AbstractPCTType
    return UndeterminedPCTType()
end


function partial_inference(::Type{Constant}, term)::AbstractPCTType
    isa(term, Int) && term > 0 && return N()
    isa(term, Int) && return I()
    isa(term, Real) && return R()
    isa(term, Complex) && return C()
end

function partial_inference(::Type{T}, terms...)::AbstractPCTType where T <: AbstractDelta
    get_type(last(terms))
end

function partial_inference(::Type{Monomial}, base::APN, power::APN)::AbstractPCTType
    escalate(get_type(base), get_type(power))
end

function inference(d::Domain)
    context = TypeContext()
    vars = vcat(variables(lower(d)), variables(upper(d)))
    for v in vars
        push_var!(context, name(v), set_type(v, base(d)))
    end

    return Domain(base(d), 
           inference(lower(d), context),
           inference(upper(d), context), 
           meta(d))
end



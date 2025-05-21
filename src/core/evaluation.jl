export evaluate, subst, variables, contains_name, eval_all, new_symbol,
    SymbolGenerator, free_and_dummy, get_free, deprimitize, scale, let_copy_to_comp

function get_free(n::APN)
    free, _ = free_and_dummy(n)
    return free
end


# Rule for evaluating the functions that can be evaluated

"""
Get the set of free and dummy variables that are in a node.
"""
function free_and_dummy(n::APN)
    all_free, outer_dummy = own_free(n), own_dummy(n)
    all_dummies = copy(outer_dummy)
    for t in content(n)
        free, dummy = free_and_dummy(t)
        free = filter(f -> !(name(f) in name.(outer_dummy)), free)
        union!(all_free, free)
        union!(all_dummies, dummy)
    end
    filter!(d -> !(name(d) in name.(all_free)), all_dummies)
    return all_free, unique(all_dummies)
end

free_and_dummy(::Constant) = Set{Var}(), Set{Var}()
free_and_dummy(v::T) where {T<:Var} = union!(Set{Var}([v]), get_free(get_type(v))), Set{Var}()

get_free(d::Domain) = union(get_free(lower(d)), get_free(upper(d)))
get_free(::AbstractPCTType) = Set{Var}()

function get_free(m::MapType)
    all_free = Set{Var}()
    for t in get_bound_type(m)
        free = get_free(t)
        union!(all_free, free)
    end
    return all_free
end

own_free(::APN) = Set{Var}()

"""
There can be free variables in the types of bound variables due to dependent types.
"""
function own_free(c::T) where {T<:Union{PermInv,Let,Map,ParametricMap}}
    all_free = Set{Var}()
    for t in get_type.(content(get_bound(c)))
        t in [C(), N(), I(), R()] && continue
        free = get_free(t)
        union!(all_free, free)
    end
    return all_free
end


own_dummy(::APN) = Set{Var}()
strip_copy(v::Var) = v
#= strip_copy(v::PCTVector) = pct_vec(strip_copy.(content(v))...) =#
strip_copy(v::Copy) = get_body(v)
strip_copy(v::TerminalNode) = v
strip_copy(v::APN) = set_terms(v, strip_copy.(terms(v))...)
function strip_copy(v::Call)
    set_terms(v, strip_copy.(terms(v))...)
end
function strip_copy(v::RevComposition)
    input_types = get_bound_type(get_type(v))
    inputs = map(var, new_symbol(v; num=length(input_types), symbol=:_z), input_types)
    outputs = pct_vec(inputs...)
    for f in reverse(content(get_body(v)))
        outputs = v_wrap(ecall(f, outputs...))
    end

    return pct_map(inputs..., v_unwrap(outputs))
end

function own_dummy(c::T) where {T<:Union{PermInv,Let,Map,ParametricMap}}
    vars = Vector{Var}()
    for b in get_bound(c)
        if isa(b, PCTVector)
            append!(vars, strip_copy.(b))
        else
            push!(vars, strip_copy(b))
        end
    end
    return Set{Var}(vars)
end

variables(::AbstractPCTType)::Vector{Var} = []
variables(d::Domain)::Vector{Var} = [variables(upper(d))..., variables(lower(d))...]
variables(d::ParametricDomain)::Vector{Var} = [get_params(d)..., variables(get_param_body(d))...]
variables(m::MapType)::Vector{Var} = vcat(variables.(get_content_type(get_bound_type(m)))..., variables(get_body_type(m)))
variables(m::ParametricMapType)::Vector{Var} = [get_params(m)..., variables(get_param_body(m))...]
variables(v::Var)::Vector{Var} = [v, variables(get_type(v))...]
variables(::Constant)::Vector{Var} = []
variables(n::APN)::Vector{Var} = vcat(variables.(terms(n))...)

function fast_rename!(n::T, old::Var, new::Symbol)::T where {T<:APN}
    for t in terms(n)
        fast_rename!(t, old, new)
    end
    return n
end

function fast_rename!(n::Var, old::Var, new::Symbol)::Var
    if name(n) == name(old)
        n.body = new
    end
    return n
end

fast_rename!(n::Constant, ::Var, ::Symbol)::Constant = n
fast_rename!(n::FieldOperators, ::Var, ::Symbol) = n


"""
Check if a name is used in a node.
"""
function contains_name(n::APN, s::Symbol)::Bool
    for t in terms(n)
        contains_name(t, s) && return true
    end
    return false
end

contains_name(v::Var, s::Symbol)::Bool = name(v) == s || contains_name(get_type(v), s)

contains_name(c::Constant, ::Symbol)::Bool = false

contains_name(c::MapType, s::Symbol)::Bool = any(t -> contains_name(t, s), [get_bound_type(c), get_body_type(c)])
contains_name(c::VecType, s::Symbol)::Bool = any(t -> contains_name(t, s), get_content_type(c))
contains_name(c::Domain, s::Symbol)::Bool = any(t -> contains_name(t, s), [upper(c), lower(c)])
contains_name(c::AbstractPCTType, s::Symbol)::Bool = false

struct SymbolGenerator
    base_symbol::Symbol
end

SymbolGenerator() = SymbolGenerator(:i)
base_symbol(g::SymbolGenerator) = g.base_symbol

Base.iterate(g::SymbolGenerator)::Tuple{Symbol,Int} = (base_symbol(g), 1)

Base.iterate(g::SymbolGenerator, state)::Tuple{Symbol,Int} = (Symbol(string(base_symbol(g), "_", state)), state + 1)

function new_symbol(nodes::Vararg{APN}; num=1, symbol=:_i)::Vector{Symbol}
    symbols = Vector{Symbol}()
    num == 0 && return symbols
    g = SymbolGenerator(symbol)
    for s in g
        flag::Bool = false
        for n in nodes
            flag = contains_name(n, s)
            flag && break
        end
        flag && continue
        length(symbols) == num && break
        push!(symbols, s)
    end
    return symbols
end

struct HashGenerator end

Base.iterate(::HashGenerator) = (:_hash_1, 1)

Base.iterate(::HashGenerator, state) = (Symbol("_hash_$(state)"), state + 1)

function new_hash(nodes...; num=1)
    symbols = Vector{Symbol}()
    for s in HashGenerator()
        any(n -> contains_name(n, s), nodes) && continue
        length(symbols) == num && return symbols
        push!(symbols, s)
    end
    return symbols
end

"""

Replacing `x(i)` with `x(j)` in `n`.

This function turns out to be mostly useless.
"""
#= function subst(n::PrimitiveCall, old::PrimitiveCall, new::AbstractCall, ::Bool)::Union{Add,PrimitiveCall}
    old == new && return n
    sub_args = map(t -> subst(t, old, new), args(n))
    if name(mapp(n)) == name(mapp(old))
        args(n) == args(old) && return new
        return add(
            delta(content(sub_args)..., content(args(old))..., new),
            delta_not(content(sub_args)..., content(args(old))..., old)
        )
    end

    set_content(n, mapp(n), sub_args)
end =#

#= subst(v::Var, ::PrimitiveCall, ::AbstractCall, ::Bool)::Var = v
subst(c::Constant, ::PrimitiveCall, ::APN, ::Bool)::Constant = c =#
function subst_type(n::ElementType, ::S, ::R, replace_dummy=false) where {S<:APN,R<:APN}
    return n
end

function subst_type(n::VecType, old::S, new::R, replace_dummy=false) where {S<:APN,R<:APN}
    return VecType(map(t -> subst_type(t, old, new, replace_dummy), get_content_type(n)))
end


function subst_type(n::Domain, old::S, new::R, replace_dummy=false) where {S<:APN,R<:APN}
    return Domain(base(n), all_subst(lower(n), old, new, replace_dummy), all_subst(upper(n), old, new, replace_dummy), meta(n))
end

function subst_type(n::MapType, old::S, new::R, replace_dummy=false) where {S<:APN,R<:APN}
    return MapType(
        subst_type(get_bound_type(n), old, new, replace_dummy),
        subst_type(get_body_type(n), old, new, replace_dummy),
        meta(n)
    )
end

function subst_type(n::ParametricMapType, old::S, new::R, replace_dummy=false) where {S<:APN,R<:APN}
    name(old) in name.(get_params(n)) && return n

    return ParametricMapType(get_params(n), subst_type(get_param_body(n), old, new, replace_dummy))
end
function subst_type(n::SplatType, old::S, new::R, replace_dummy=false) where {S<:APN,R<:APN}
    return SplatType(subst_type(get_body_type(n), old, new, replace_dummy))

end

function all_subst(n::T, old::S, new::R, replace_dummy=false) where {T<:APN,S<:APN,R<:APN}
    result = subst(n, old, new, replace_dummy)
    return set_type(result, subst_type(get_type(result), old, new, replace_dummy))
end

subst(c::Constant, ::Var, ::APN, ::Bool)::Constant = c

function subst(n::Var, old::Var, new::APN, ::Bool)
    # The type of the variable is not compared.
    name(n) == name(old) ? new : n
end

function subst(n::T, old::T, new::APN, ::Bool) where {T<:APN}
    n == old ? new : n
end

function subst(n::T, old::S, new::R, replace_dummy=false) where {T<:APN,S<:APN,R<:APN}
    new = R == Call ? eval_all(new) : new
    if !replace_dummy
        free, dummies = free_and_dummy(n)
        name(old) in name.(dummies) && return n
        # name(old) in name.(free) || return n
        n = resolve_conflict(n, old, new, dummies)
    end

    return reconstruct(n, old, new, replace_dummy)
end

function reconstruct(n::APN, old::APN, new::APN, replace_dummy::Bool)
    return set_terms(n, [all_subst(t, old, new, replace_dummy) for t in terms(n)]...)
end

function reconstruct(n::PrimitiveCall, old::APN, new::APN, replace_dummy::Bool)
    new_args = map(t -> all_subst(t, old, new), content(args(n)))
    new_map = all_subst(mapp(n), old, new, replace_dummy)
    return call(new_map, new_args...)
end

#= function reconstruct(n::PrimitiveCall, old::APN, new::Map, replace_dummy::Bool)
    new_args = map(t -> subst(t, old, new), content(args(n)))
    if name(mapp(n)) == name(old)
        return call(new, map(t -> subst(t, old, new, replace_dummy), new_args)...)
    else
        return call(mapp(n), new_args...)
    end
end =#


#= """
TODO: This must change
The dummy variables are not allowed to be a `PrimitiveCall`, so
we don't have to consider replacing the dummy variabless.
"""
function subst(n::T, old::PrimitiveCall, new::APN, replace_dummy=false) where {T<:APN}
    if !replace_dummy
        _, dummies = free_and_dummy(n)

        name(mapp(old)) in name.(dummies) && return n
        n = resolve_conflict(n, old, new)
    end

    return set_terms(n, [subst(t, old, new, replace_dummy) for t in terms(n)]...)
end
 =#
"""
If free variables of new collide with dummy variables in n
replace the dummies with something new.
sum(i, i * sum(j, A(i, j)))
"""
function resolve_conflict(n::T, old::APN, new::APN,
    n_dummies=last(free_and_dummy(n))) where {T<:APN}
    conflict = Vector{Var}()
    new_free, _ = free_and_dummy(new)
    for d in n_dummies
        name(d) in name.(new_free) && push!(conflict, d)
    end
    isempty(conflict) && return n

    for c in conflict
        new_prefix = filter(t -> t != "", split(string(name(c)), "_")) |> first
        tmp = set_content(c, first(new_symbol(new, n, old, symbol=Symbol("_$(new_prefix)"))))
        n = all_subst(n, c, tmp, true)
    end
    return n
end


evaluate(n::APN) = set_content(n, map(evaluate, content(n))...)

function evaluate(c::AbstractCall)
    set_content(c, evaluate(mapp(c)), map(evaluate, args(c)))
end

evaluate(c::TerminalNode) = c

function parametric_evaluation(c::Call)
    pm = mapp(c)
    @assert isa(pm, AbstractMap)
    m = get_body(pm)
    type_vars = get_bound(pm)
    values = Dict()
    type_match!([type_vars...], values, get_bound_type(get_type(m)), get_type(args(c)))
    eval_all(call(pct_map(type_vars..., call(m, args(c)...)), [values[t] for t in type_vars]...))
end

function call_on_sum_let(c::Call, i)
    s = args(c)[i]
    if isa(s, Sum)
        new_args = [args(c)[1:i-1]..., get_body(s), args(c)[i+1:end]...]
    elseif isa(s, Splat)
        s = get_body(s)
        new_args = [args(c)[1:i-1]..., get_body(s)..., args(c)[i+1:end]...]
    else
        error("type $(typeof(s)) is not supported out of call.")
    end

    new_map_var = var(first(new_symbol(c)), get_type(mapp(c)))
    l = get_body(s)
    result = evaluate(call(pct_map(new_map_var,
            pct_sum(get_bound(s)...,
                pct_let(
                    get_bound(l)..., args(l)...,
                    call(new_map_var, new_args...)))), mapp(c)))
    return result
end

function call_on_let(c::Call, i)
    l = args(c)[i]
    if isa(l, Let)
        new_args = [args(c)[1:i-1]..., get_body(l), args(c)[i+1:end]...]
    elseif isa(l, Splat)
        l = get_body(l)
        new_args = [args(c)[1:i-1]..., get_body(l)..., args(c)[i+1:end]...]
    else
        error("type $(typeof(l)) is not supported out of call.")
    end
    #= println(pretty.(new_args)) =#

    new_map_var = var(first(new_symbol(c)), get_type(mapp(c)))
    result = evaluate(call(pct_map(new_map_var, pct_let(
            get_bound(l)..., args(l)...,
            call(new_map_var, new_args...))), mapp(c)))
    return result
end

function evaluate(c::Call)
    isa(get_type(mapp(c)), ParametricMapType) && return parametric_evaluation(c)
    isa(mapp(c), Call) && return evaluate(call(eval_all(mapp(c)), args(c)...))
    isa(mapp(c), Add) && return add(map(t -> eval_all(call(t, args(c)...)), content(get_body(mapp(c))))...)

    new_args = map(eval_all, args(c))

    i = findfirst(a -> isa(a, AbstractLet) || (isa(a, Splat) && isa(get_body(a), AbstractLet)), content(args(c)))
    i === nothing || return evaluate(call_on_let(c, i))

    j = findfirst(a -> isa(a, Sum) && isa(get_body(a), AbstractLet) || (isa(a, Splat) && isa(get_body(a), Sum) && isa(get_body(get_body(a)), AbstractLet)), content(args(c)))
    j === nothing || return evaluate(call_on_sum_let(c, j))

    if any(t -> isa(get_type(t), SplatType), new_args)
        return call(mapp(c), new_args...)
    end
    new_bound = map(var, new_symbol(c, num=length(get_bound_type(get_type(mapp(c)))), symbol=:_e), get_bound_type(get_type(mapp(c))))
    new_args = filter(a -> !(isa(get_type(a), VecType) && (length(get_type(a)) == 0)), content(new_args))
    if length(new_bound) == 0
        n = evaluate(get_body(mapp(c)))
        return n
    end
    @assert isa(mapp(c), AbstractMap)
    @assert length(new_bound) == length(new_args)
    @assert length(new_bound) == length(get_bound(mapp(c)))

    n = evaluate(get_body(mapp(c)))
    for (old, new) in zip(content(get_bound(mapp(c))), new_bound)
        n = all_subst(n, old, new)
    end

    for (old, new) in zip(new_bound, new_args)
        n = all_subst(n, old, new)
    end

    return n
end


function evaluate(l::Let)
    copies, substs, subst_args, copy_args = [], [], [], []
    for (b, a) in zip(get_bound(l), args(l))
        if isa(b, Copy) || (isa(b, PCTVector) && all(t -> isa(t, Copy), content(b)))
            push!(copies, b)
            push!(copy_args, eval_all(a))
        else
            push!(substs, b)
            push!(subst_args, eval_all(a))
        end
    end

    function subst_all(substs, subst_args, body)
        isempty(substs) && return body
        old, substs... = substs
        new, subst_args... = subst_args
        subst_args = map(t -> subst(t, old, new), subst_args)
        return subst_all(substs, subst_args, subst(body, old, new))
    end
    new_call = evaluate(get_body(l))

    if !isempty(substs)
        # TODO: Bug! This does not consider the case where one variable is part of the other.
        #= for i in length(substs)
            old, new = substs[i], subst_args[i]
            for j in i+1:length(substs)
                subst_args[j] = ecall(pct_map(old, subst_args[j]), new)
            end
            new_call = ecall(pct_map(old, new_call), new)
        end =#
        new_call = subst_all(substs, subst_args, new_call)
        #= new_call = evaluate(call(pct_map(substs..., get_body(l)), subst_args...)) =#
    end
    result = pct_let(copies..., copy_args..., new_call)
    return result
end

function let_copy_to_comp(zs::APN, l::Let)
    bound, args, body = content(l)

    function filter_states(states, i)
        remains = Vector{APN}()
        for s in states
            s in get_free(body) || any(j -> s in get_free(args[j]), i+1:length(args)) || continue
            push!(remains, s)
        end
        return pct_vec(remains...)
    end

    state_vars::PCTVector = v_wrap(zs)
    funcs = Vector{Any}()
    for i in 1:length(bound)
        filtered = filter_states(state_vars, i)
        push!(funcs, pct_map(state_vars..., pct_vec(args[i], filtered...)))
        state_vars = filtered
        state_vars = pct_vec(strip_copy(bound[i]), state_vars...)
        #= pushfirst!(content(state_vars), strip_copy(bound[i])) =#
    end
    push!(funcs, pct_map(state_vars..., body))
    return call(rev_composite(reverse(funcs)...), v_wrap(zs)...)
end


has_call(n::APN) = any(has_call, content(n))
has_call(::TerminalNode) = false
has_call(::Copy) = false

function has_call(c::Call)
    has_call(mapp(c)) && return true
    any(has_call, content(args(c))) && return true
    (isa(mapp(c), PCTVector) && length(args(c)) == 1 && isa(first(args(c)), Constant)) && return true
    isa(mapp(c), Map) && !any(t -> isa(get_type(t), SplatType), args(c)) && return true
    return false
end

function has_call(lt::Let)
    has_call(get_body(lt)) && return true
    any(has_call, args(lt)) && return true
    any(t -> isa(t, Var), get_bound(lt)) && return true
    return false
end


function eval_all(n::APN)
    while has_call(n)
        n = evaluate(n)
    end
    return n
end

function deprimitize(n::APN)
    return set_terms(n, map(deprimitize, terms(n))...)
end

function deprimitize(p::PrimitivePullback)
    return pullback(get_body(p))
end

deprimitize(t::TerminalNode) = t

scale(n::APN, c::Int) = mul(constant(c), n)
scale(n::Map, c::Int) = pct_map(get_bound(n)..., scale(get_body(n), c))




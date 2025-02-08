export evaluate, subst, variables, contains_name, eval_all, new_symbol, SymbolGenerator, free_and_dummy, get_free, deprimitize, scale, let_copy_to_call

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
free_and_dummy(v::T) where {T<:Var} = Set{Var}([v]), Set{Var}()

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

function own_free(c::T) where {T<:Union{PermInv,Let,Map}}
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
strip_copy(v::Copy) = get_body(v)

function own_dummy(c::T) where {T<:Union{PermInv,Let,Map}}
    return Set{Var}(map(strip_copy, content(get_bound(c))))
end

variables(v::Var)::Vector{Var} = [v]
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

evaluate(c::AbstractCall) = set_content(c, evaluate(mapp(c)), map(evaluate, args(c)))

evaluate(c::TerminalNode) = c

function evaluate(c::Call)
    isa(mapp(c), Call) && return evaluate(call(eval_all(mapp(c)), args(c)...))
    isa(mapp(c), Add) && return add(map(t -> eval_all(call(t, args(c)...)), content(get_body(mapp(c))))...)

    new_bound = map(var, new_symbol(c, num=length(get_bound(mapp(c))), symbol=:_e), get_type(get_bound(mapp(c))))
    @assert length(new_bound) == length(args(c)) == length(get_bound(mapp(c)))

    n = evaluate(get_body(mapp(c)))
    for (old, new) in zip(content(get_bound(mapp(c))), new_bound)
        n = all_subst(n, old, new)
    end
    new_args = map(eval_all, args(c))

    for (old, new) in zip(new_bound, new_args)
        n = all_subst(n, old, new)
    end

    return n
end


function evaluate(l::Let)
    copies, substs, subst_args, copy_args = [], [], [], []
    for (b, a) in zip(get_bound(l), args(l))
        if isa(b, Copy)
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

let_copy_to_call(x::APN) = set_content(x, map(let_copy_to_call, content(x))...)

let_copy_to_call(x::Union{TerminalNode,Copy}) = x

function let_copy_to_call(x::Let)
    bound, args, body = let_copy_to_call.(content(x))
    for b in bound
        isa(b, Copy) || error("$(pretty(b)) should be inlined first")
    end

    #= result = body
    for (b, a) in zip(bound, args)
        result = primitive_call(pct_map(strip_copy(b), body), a)
    end =#

    result = foldr(((b, a), res) -> primitive_call(
            pct_map(strip_copy(b), res), a), zip(bound, args); init=body)

    return result

end


has_call(n::APN) = any(has_call, content(n))
has_call(::TerminalNode) = false
has_call(::Copy) = false

function has_call(c::Call)
    has_call(mapp(c)) ||
        any(has_call, content(args(c))) ||
        (isa(mapp(c), PCTVector) && length(args(c)) == 1 && isa(first(args(c)), Constant)) ||
        isa(mapp(c), Map)
end
function has_call(lt::Let)
    has_call(get_body(lt)) && return true
    any(has_call, args(lt)) && return true
    return any(t -> !isa(t, Copy), get_bound(lt))
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


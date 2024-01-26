export evaluate, subst, variables, contains_name, eval_all, new_symbol, SymbolGenerator, free_and_dummy

# Rule for evaluating the functions that can be evaluated

"""
Get the set of free and dummy variables that are in a node.
"""
function free_and_dummy(n::APN)
    all_free, outer_dummy = Set{Var}(), own_dummy(n)
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

own_dummy(::APN) = Set{Var}()

function own_dummy(c::Contraction)
    return Set{Var}(content(ff(c)))
end

function own_dummy(m::Map)
    extract_var(n::Var) = [n]
    extract_var(n::PrimitiveCall) = [mapp(n), content(args(n))...]
    return Set{Var}(vcat(map(extract_var, content(ff(m)))...))
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
        n.content = new
    end
    return n
end

fast_rename!(n::Constant, ::Var, ::Symbol)::Constant = n


"""
Check if a name is used in a node.
"""
function contains_name(n::APN, s::Symbol)::Bool
    for t in terms(n)
        contains_name(t, s) && return true
    end
    return false
end

contains_name(v::Var, s::Symbol)::Bool = name(v) == s

contains_name(c::Constant, ::Symbol)::Bool = false

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
subst(c::Constant, ::Var, ::APN, ::Bool)::Constant = c

function subst(n::Var, old::Var, new::APN, ::Bool)
    # The type of the variable is not compared.
    name(n) == name(old) ? new : n
end

function subst(n::T, old::T, new::APN, ::Bool) where T <: APN
    n == old ? new : n
end

function subst(n::T, old::S, new::R, replace_dummy=false) where {T<:APN,S<:APN,R<:APN}
    new = R == Call ? eval_all(new) : new
    if !replace_dummy
        _, dummies = free_and_dummy(n)
        name(old) in name.(dummies) && return n
        n = resolve_conflict(n, old, new, dummies)
    end

    return reconstruct(n, old, new, replace_dummy)
end

function reconstruct(n::APN, old::APN, new::APN, replace_dummy::Bool)
    return set_terms(n, [subst(t, old, new, replace_dummy) for t in terms(n)]...)
end

function reconstruct(n::PrimitiveCall, old::APN, new::APN, replace_dummy::Bool)
    new_args = map(t -> subst(t, old, new), content(args(n)))
    new_map = subst(mapp(n), old, new, replace_dummy)
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
        new_prefix = filter(t->t != "", split(string(name(c)), "_")) |> first
        tmp = set_content(c, first(new_symbol(new, n, old, symbol=Symbol("_$(new_prefix)"))))
        n = subst(n, c, tmp, true)
    end
    return n
end


evaluate(n::APN) = set_content(n, map(evaluate, content(n))...)

evaluate(c::AbstractCall) = set_content(c, evaluate(mapp(c)), map(evaluate, args(c)))

evaluate(c::TerminalNode) = c

function evaluate(c::Call)
    new_from = map(var, range.(ff(mapp(c))), new_symbol(c, num=length(ff(mapp(c))), symbol=:_e), get_type(ff(mapp(c))))
    @assert length(new_from) == length(args(c)) == length(ff(mapp(c)))

    n = evaluate(fc(mapp(c)))
    for (old, new) in zip(content(ff(mapp(c))), new_from)
        n = subst(n, old, new)
    end
    new_args = map(eval_all, args(c))

    for (old, new) in zip(new_from, new_args)
        n = subst(n, old, new)
    end

    return n
end

function evaluate(l::Let)
    new_call = call(pct_map(ff(l)..., fc(l)), args(l)...)
    return evaluate(new_call)
end

has_call(n::APN) = any(has_call, content(n))
has_call(::TerminalNode) = false
has_call(::Call) = true
has_call(::Let) = true

function eval_all(n::APN)
    while has_call(n)
        n = evaluate(n)
    end
    return n
end


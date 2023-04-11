export evaluate, subst, dummy_vars, variables, contains_name, eval_all, new_symbol, SymbolGenerator

# Rule for evaluating the functions that can be evaluated

"""
Get the set of dummy variables that are in a node.
"""
dummy_vars(::APN) = Vector{APN}()

dummy_vars(c::Contraction) = from(c)

function dummy_vars(m::Map)
    extract_var(n::Var) = [n]
    extract_var(n::PrimitiveCall) = [mapp(n), content(args(n))...]
    vcat(dummy_vars(fc(m)), map(extract_var, content(ff(m)))...)
end

variables(v::Var) = [v]
variables(::Constant) = []
variables(n::APN) = vcat(variables.(content(n))...)


"""
Check if a name is used in a node.
"""
contains_name(n::APN, s::Symbol) = any(t->contains_name(t, s), terms(n))

contains_name(v::Var, s::Symbol) = name(v) == s

contains_name(c::Constant, ::Symbol) = false

struct SymbolGenerator end

Base.iterate(::SymbolGenerator) = (:i_0, 1)

Base.iterate(::SymbolGenerator, state) = (Symbol("i_$(state)"), state+1)

function new_symbol(nodes...; num = 1)
    symbols = Vector{Symbol}()
    g = SymbolGenerator()
    for s in g
        any(n->contains_name(n, s), nodes) && continue
        length(symbols) == num && return symbols
        push!(symbols, s)
    end
    return symbols
end

struct HashGenerator end

Base.iterate(::HashGenerator) = (:_hash_1, 1)

Base.iterate(::HashGenerator, state) = (Symbol("_hash_$(state)"), state+1)

function new_hash(nodes...; num = 1)
    symbols = Vector{Symbol}()
    for s in HashGenerator()
        any(n->contains_name(n, s), nodes) && continue
        length(symbols) == num && return symbols
        push!(symbols, s)
    end
    return symbols
end


function subst(n::Var, old::Var, new::APN)
    name(n) == name(old) || return n
    #= get_type(n) == get_type(old) || error("type mismatch: $(get_type(n)) vs $(get_type(old))") =#
    return new
end

"""

Replacing `x(i)` with `x(j)` in `n`.

This function turns out to be mostly useless.
"""
function subst(n::PrimitiveCall, old::PrimitiveCall, new::AbstractCall)
    old == new && return n
    sub_args = map(t->subst(t, old, new), args(n))
    if name(mapp(n)) == name(mapp(old))
        args(n) == args(old) && return new
        return add(
            delta(content(sub_args)..., content(args(old))..., new), 
            delta_not(content(sub_args)..., content(args(old))..., old) 
        )
    end

    set_content(n, mapp(n), sub_args)
end

subst(v::Var, ::PrimitiveCall, ::AbstractCall) = v
subst(c::Constant, ::Var, ::APN) = c
subst(c::Constant, ::PrimitiveCall, ::APN) = c

function subst(n::T, old::Var, new::APN, replace_dummy=false) where T <: APN
    dummies = dummy_vars(n)

    # Unless we are explicitly replacing the dummy variables, 
    # the dummy variables are not variables and `subst` does nothing.
    !replace_dummy && name(old) in name.(dummies) && return n

    # New node contains dummy variables.
    #= conflict = filter(d->contains_name(new, name(d)), dummies)

    !isempty(conflict) || return set_terms!(n, map(t->subst(t, old, new), terms(n))...)

    # Resolve the conflicts.
    for c in conflict
        # tmp = Var(new_symbol(new, n, old), get_type(c))
        tmp = set_content!(c, new_symbol(new, n, old))
        n = subst(n, c, tmp, true)
    end =#
    n = resolve_conflict(n, old, new)

    return set_terms(n, map(t->subst(t, old, new), terms(n))...)
end


"""

The dummy variables are not allowed to be a `PrimitiveCall`, so
we don't have to consider replacing the dummy variabless.
"""
function subst(n::T, old::PrimitiveCall, new::APN) where T <: APN
    dummies = dummy_vars(n)

    name(mapp(old)) in name.(dummies) && return n

    #= conflict = filter(d->contains_name(new, name(d)), dummies)

    !isempty(conflict) || return set_terms!(n, map(t->subst(t, old, new), terms(n))...)

    for c in conflict
        tmp = set_content!(c, new_symbol(new, n, old))
        n = subst(n, c, tmp, true)
    end =#
    n = resolve_conflict(n ,old, new)

    return set_terms(n, map(t->subst(t, old, new), terms(n))...)
    #= return subst(n, old, new) =#
end

function resolve_conflict(n::APN, old::APN, new::APN)
    conflict = filter(d->contains_name(new, name(d)), dummy_vars(n))
    isempty(conflict) && return n

    for c in conflict
        tmp = set_content(c, first(new_symbol(new, n, old)))
        n = subst(n, c, tmp, true)
    end
    return n
end


evaluate(n::APN) = set_content(n, map(evaluate, content(n))...)

evaluate(c::AbstractCall) = set_content(c, evaluate(mapp(c)), map(evaluate, args(c)))

evaluate(c::TerminalNode) = c

function evaluate(c::Call)
    n = evaluate(fc(mapp(c)))
    for (old, new) in zip(content(ff(mapp(c))), content(args(c))) 
        n = subst(n, old, new)
    end
    return n
end

has_call(n::APN) = any(has_call, content(n))
has_call(::TerminalNode) = false
has_call(::Call) = true

function eval_all(n::APN) 
    while has_call(n) 
        n = evaluate(n) 
    end
    return n
end


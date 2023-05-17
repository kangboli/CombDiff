export evaluate, subst, dummy_vars, variables, contains_name, eval_all, new_symbol, SymbolGenerator, free_variables

# Rule for evaluating the functions that can be evaluated

"""
Get the set of dummy variables that are in a node.
"""
#= function dummy_vars(n::APN) 
    vcat(dummy_vars.(content(n))...)
end
dummy_vars(t::TerminalNode) = Vector{APN}() =#

dummy_vars(::APN) =  Vector{APN}()

function dummy_vars(c::T) where T <: Union{Contraction, Prod}
    content(ff(c))
end

function dummy_vars(m::Map)
    extract_var(n::Var) = [n]
    extract_var(n::PrimitiveCall) = [mapp(n), content(args(n))...]
    vcat(map(extract_var, content(ff(m)))...)
end

dummy_all(n::APN) = vcat(dummy_vars(n), map(dummy_vars, terms(n))...)

variables(v::Var)::Vector{Var} = [v]
variables(::Constant)::Vector{Var} = []
variables(n::APN)::Vector{Var} = vcat(variables.(terms(n))...)

function free_variables(n::APN) 
    free = Vector{APN}()
    dummies = dummy_all(n)
    for v in variables(n)
        (v in dummies || v in free) && continue
        push!(free, v)
    end
    return free
end


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
    namespace::Symbol
end

Base.iterate(g::SymbolGenerator)::Tuple{Symbol, Int} = (Symbol(string(g.namespace, "_0")), 1)

Base.iterate(g::SymbolGenerator, state)::Tuple{Symbol, Int} = (Symbol(string(g.namespace, "_", state)), state+1)

function new_symbol(nodes::Vararg{APN}; num = 1, namespace=:i)::Vector{Symbol}
    symbols = Vector{Symbol}()
    g = SymbolGenerator(namespace)
    #= name_used = (n::APN)->contains_name(n, s) =#
    for s in g
        flag::Bool = false
        for n in nodes
            flag = contains_name(n, s) 
            flag && break
        end
        flag && continue
        #= any(name_used, nodes) && continue =#
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


"""
Substituting a vector of variable is done by substituting them one by one.
"""
function subst(n::APN, old::PCTVector, new::PCTVector)
    for (i, j) in zip(content(old), content(new))
        n = subst(n, i, j)
    end
    return n
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
function subst(n::PrimitiveCall, old::PrimitiveCall, new::AbstractCall)::Union{Add, PrimitiveCall}
    old == new && return n
    sub_args = map(t->subst(t, old, new), args(n))
    if name(mapp(n)) == name(mapp(old))
        args(n) == args(old) && return new
        return add(
            delta(sub_args, args(old), new), 
            delta_not(sub_args, args(old), old) 
        )
    end

    set_content(n, mapp(n), sub_args)
end

subst(v::Var, ::PrimitiveCall, ::AbstractCall)::Var = v
subst(c::Constant, ::Var, ::APN)::Constant = c
subst(c::Constant, ::PrimitiveCall, ::APN)::Constant = c

function subst(n::T, old::Var, new::APN, replace_dummy=false) where T <: APN
    dummies = dummy_vars(n)

    # Unless we are explicitly replacing the dummy variables, 
    # the dummy variables are not variables and `subst` does nothing.
    !replace_dummy && name(old) in name.(dummies) && return n

    # New node contains dummy variables.
    #= conflict = filter(d->contains_name(new, name(d)), dummies) =#
    #= !isempty(conflict) || return set_terms!(n, [subst(t, old, new) for t in terms(n)]...) =#

    n = resolve_conflict(n, old, new)

    return set_terms(n, [subst(t, old, new) for t in terms(n)]...)
end


"""

The dummy variables are not allowed to be a `PrimitiveCall`, so
we don't have to consider replacing the dummy variabless.
"""
function subst(n::T, old::PrimitiveCall, new::APN) where T <: APN
    dummies = dummy_vars(n)
    name(mapp(old)) in name.(dummies) && return n
    n = resolve_conflict(n ,old, new)

    return set_terms(n, [subst(t, old, new) for t in terms(n)]...)
end

function resolve_conflict(n::APN, old::APN, new::APN)
    conflict = Vector{Var}()
    for d in dummy_vars(n)
        contains_name(new, name(d)) && push!(conflict, d)
    end
    #= conflict = filter(d->contains_name(new, name(d)), dummy_vars(n)) =#
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
    #= for (old, new) in zip(content(ff(mapp(c))), content(args(c))) 
        n = subst(n, old, new)
    end =#
    n = subst(n, ff(mapp(c)), args(c))
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


export @cascade, combine_add, minimize_node!

macro cascade(f)
    esc(:(begin
        PCT.$(f)(n::APN) = set_terms!(n, map(PCT.$(f), terms(n))...)
        PCT.$(f)(t::TerminalNode) = t
    end))
end

function combine_add(s::Add)
    d = Dict()
    one = make_node!(Constant, 1)
    process_term!(t::APN) = d[t] = get!(d, t, 0) + 1
    process_term!(c::Constant) = d[one] = get!(d, c, 0) + content(c)
    process_term!(m::Mul) = let (c, n) = split_constant(m)
        d[n] = get!(d, n, 0) + content(c)
    end
    map(process_term!, content(s))
    filter!(((k, v),)->abs(v) > 1e-7, d)

    mul_term(k, v) = v == 1 ? k : make_node!(Mul, make_node!(PCTVector, make_node!(Constant, v), k))
    make_node!(Add, make_node!(PCTVector, [combine_add(mul_term(k, v)) for (k, v) in d]...))
end

@cascade combine_add

minimize_node!(n::Var) = n

delta_reducible(i::Var, n::APN) = any(t->delta_reducible(i, t), content(n))

function delta_reducible(i::Var, n::Contraction) 
    i in content(ff(n)) && return false
    return invoke(delta_reducible, (Var, APN), i, n)
end

function delta_reducible(i::Var, d::Delta)
    (i in content(upper(d)) || i in content(lower(d))) && return true
    return invoke(delta_reducible, (Var, APN), i, d)
end

function delta_reducible(i::Var, m::Map)
    i in content(ff(m)) && return false
    return invoke(delta_reducible, (Var, APN), i, m)
end

delta_reducible(::Var, ::AbstractCall) = false

delta_reducible(::Var, ::TerminalNode) = false

delta_reducible(::Var, ::Pullback) = error("Pullbacks should be evaluated before minimization.")

delta_reducible(::Var, ::PrimitivePullback) = false



delta_reduce(i::Var, n::Union{PrimitiveCall, TerminalNode}, ::Type{T}) where T <: Contraction =
    make_node!(T,  make_node!(PCTVector, i), n)

"""
Assume at least one of the terms is reducible.
"""
function delta_reduce(i::Var, n::Add, ::Type{T}) where T <: Contraction
    reduce_if_reducible(n::APN) = delta_reducible(i, n) ? delta_reduce(i, n, T) : make_node!(T, make_node!(PCTVector, i), n)
    set_content!(n, make_node!(PCTVector, map(reduce_if_reducible, content(fc(n)))...))
end

"""
Assume at least one of the terms is reducible.
"""
function delta_reduce(i::Var, m::Mul, ::Type{T}) where T <: Contraction
    reduce_if_reducible(n::APN) = delta_reducible(i, n) ? delta_reduce(i, n, T) : n 
    set_content!(m, make_node!(PCTVector, map(reduce_if_reducible, content(fc(m)))...))
end


function delta_reduce(i::Var, d::Delta, ::Type{T}) where T <: Contraction
    (i in content(upper(d)) || i in content(lower(d))) || 
    return make_node!(Delta, upper(d), lower(d), delta_reduce(i, last(content(d)), T))

    index = findfirst(x->x==i, content(upper(d))) 
    if index !== nothing
        j = content(lower(d))[index]
    else
        index = findfirst(x->x==i, content(lower(d))) 
        j = content(upper(d))[index]
    end

    new_upper = deleteat!(content(upper(d)), index)
    new_lower = deleteat!(content(lower(d)), index)

    new_content = subst(last(content(d)), i, j)
    length(new_upper) == 0 && return new_content
    return make_node!(Delta, make_node!(PCTVector, new_upper), make_node!(PCTVector, new_lower), new_content)
end


function minimize_node!(c::T) where T <: Contraction
    reducible = filter(t->delta_reducible(t, fc(c)), content(ff(c)))
    irreducible = filter(t->!delta_reducible(t, fc(c)), content(ff(c)))

    n = fc(c)
    for i in reducible
        n = delta_reduce(i, n, T)
    end

    length(irreducible) == 0 && return n
    return make_node!(T, make_node!(PCTVector, delta_reducible), n)
end

function minimize_node!(n::APN)
    set_content!(n, minimize_node!(fc(n)))
end


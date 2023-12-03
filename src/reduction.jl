export @cascade, combine_add,  delta_reduce, delta_reducible

macro cascade(f)
    esc(:(begin
        PCT.$(f)(n::APN) = set_terms(n, map(PCT.$(f), terms(n))...)
        PCT.$(f)(t::TerminalNode) = t
    end))
end

function combine_add(s::Add)
    d = Dict()
    one = make_node(Constant, 1)
    process_term!(t::APN) = d[t] = get!(d, t, 0) + 1
    process_term!(c::Constant) = d[one] = get!(d, c, 0) + content(c)
    process_term!(m::Mul) = let (c, n) = split_constant(m)
        d[n] = get!(d, n, 0) + content(c)
    end
    map(process_term!, content(s))
    filter!(((k, v),)->abs(v) > 1e-7, d)

    mul_term(k, v) = v == 1 ? k : mul(make_node(Constant, v), k)
    add([combine_add(mul_term(k, v)) for (k, v) in d]...)
end

@cascade combine_add

minimize_node!(n::Var) = n

delta_reducible(i::Var, n::APN) = any(t->delta_reducible(i, t), content(n))

function delta_reducible(i::Var, n::Contraction) 
    i  == ff(n) && return false
    return invoke(delta_reducible, Tuple{Var, APN}, i, n)
end

function delta_reducible(i::Var, d::Delta)
    any(t->contains_name(t, name(i)), [lower(d), upper(d)]) && return true
    return invoke(delta_reducible, Tuple{Var, APN}, i, d)
end

function delta_reducible(i::Var, m::Map)
    (i  in content(ff(m))) && return false
    return invoke(delta_reducible, Tuple{Var, APN}, i, m)
end

delta_reducible(::Var, ::AbstractCall) = false

delta_reducible(::Var, ::TerminalNode) = false

delta_reducible(::Var, ::Pullback) = error("Pullbacks should be evaluated before minimization.")

delta_reducible(::Var, ::PrimitivePullback) = false

delta_reduce(i::Var, n::Union{PrimitiveCall, TerminalNode}, ::Type{T}) where T <: Contraction =
    make_node(T,  make_node(PCTVector, i), n)

"""
Assume at least one of the terms is reducible.
"""
function delta_reduce(i::Var, n::Add, ::Type{T}) where T <: Contraction
    reduce_if_reducible(n::APN) = delta_reducible(i, n) ? delta_reduce(i, n, T) : make_node(T, make_node(PCTVector, i), n)
    set_content(n, make_node(PCTVector, map(reduce_if_reducible, content(fc(n)))...))
end

"""
Assume at least one of the terms is reducible.
"""
function delta_reduce(i::Var, m::Mul, ::Type{T}) where T <: Contraction
    reduce_if_reducible(n::APN) = delta_reducible(i, n) ? delta_reduce(i, n, T) : n 
    set_content(m, make_node(PCTVector, map(reduce_if_reducible, content(fc(m)))...))
end


function delta_reduce(i::Var, d::Delta, ::Type{T}) where T <: Contraction
    (i == upper(d) || i == lower(d)) || 
    return make_node(Delta, upper(d), lower(d), delta_reduce(i, last(content(d)), T))

    j = i == upper(d) ? lower(d) : upper(d)

    return  subst(last(content(d)), i, j)
end

function delta_reduce(i::Var, n::APN, ::Type{T}) where T <: Contraction
    set_content(n, delta_reduce(i, fc(n), T))
end


function delta_reduce(c::T) where T <: Contraction
    reduced_content = delta_reduce(fc(c))
    delta_reducible(ff(c), reduced_content) || return set_content(c, reduced_content)
    return delta_reduce(ff(c), reduced_content, T)
end


function delta_reduce(n::APN)
    #= println.(pretty.(map(delta_reduce, content(n)))) =#
    set_content(n, map(delta_reduce, content(n))...)
end

delta_reduce(n::TerminalNode) = n
    


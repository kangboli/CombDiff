export pb, pbs 

"""
pb((x, y) -> f(x, y)) = [(x, y, k) -> pb(x->f(x, y))(x, k), (x, y, k) -> pb(y->f(x, y))(y, k)]

"""
function pb(ff_and_fc::Vararg{APN})
    z_s = ff_and_fc[1:end-1]
    ov = last(ff_and_fc)
    k = var(:_K, get_type(ov))
    function dispatcher(z, ov)
        isa(get_type(z), ElementType) && isa(get_type(ov), ElementType) && return pbs
        isa(get_type(z), MapType) && isa(get_type(ov), ElementType) && return functional
        isa(get_type(z), ElementType) && isa(get_type(ov), MapType) && return parametrization
        isa(get_type(z), MapType) && isa(get_type(ov), MapType) && return functor
    end

    [map(z -> pct_map(z_s..., k, call(dispatcher(z, ov)(z, ov), z, k)), z_s)...]
end

function pbs(z::Var, ov::Var)
    k = var(:_K, get_type(ov))
    name(z) == name(ov) && return pct_map(z, k, k)
    return pct_map(z, k, constant(0))
end

"""
𝒫(z->f(z)') = (z, k) -> 𝒫(z->f(z))(z, k')
"""
function pbs(z::APN, ov::Conjugate)
    k = var(:_K, get_type(ov))
    ph = pbs(z, fc(ov))
    pct_map(z, k, call(ph, z, conjugate(k)))
end


"""
f(z) = g1(z) + g2(z)
Pf = (z, k) -> P(z->g1(z))(z, k) + P(z->g2(z))(z, k)
"""
function pbs(z::APN, ov::Add)
    k = var(:_K, get_type(ov))
    terms = map(c -> call(pbs(z, c), z, k), content(fc(ov)))
    pct_map(z, k, add(terms...))
end


function pbs(z::APN, ov::Mul)
    k = var(:_K, get_type(ov))
    terms::PCTVector = fc(ov)
    t1 = fc(terms)
    rest = length(terms) > 2 ? mul(content(terms)[2:end]...) : last(terms)

    arg_1 = mul(conjugate(rest), k)
    arg_2 = mul(conjugate(t1), k)
    term_1 = call(pbs(z, t1), z, arg_1)
    term_2 = call(pbs(z, rest), z, arg_2)
    pct_map(z, k, add(term_1, term_2))
end


function functional(z::APN, ov::APN)
    k = var(:_K, get_type(ov))
    a_types = from(get_type(z))
    a_index_symbols = new_symbol(z, ov, k; num=length(a_types))
    #= println(a_index_symbols) =#
    a = map((s, t) -> var(s, t), a_index_symbols, content(a_types))
    #= println(pretty.(a)) =#

    za = call(z, a...)
    pct_map(z, k, pct_map(a..., call(pbs(za, ov), za, k)))

end

function parametrization(z::APN, ov::APN)
    k = var(:_K, get_type(ov))
    result_map_type = get_type(ov)
    sum_types = content(from(result_map_type))
    sum_index_symbols = new_symbol(z, ov, k; num=length(sum_types))
    b = map((s, t) -> var(s, t), sum_index_symbols, content(sum_types))

    kb = call(k, b...)
    fb = call(ov, b...)
    pct_map(z, k, pct_sum(b..., call(pbs(z, fb), z, kb)))
end

function functor(z::APN, ov::APN)
    k = var(:_K, get_type(ov))
    a_types = from(get_type(z))
    a_index_symbols = new_symbol(z, ov, k; num=length(a_types))
    a = map((s, t) -> var(s, t), a_index_symbols, content(a_types))


    k = var(:_K, get_type(ov))
    result_map_type = get_type(ov)
    sum_types = content(from(result_map_type))
    sum_index_symbols = new_symbol(z, ov, k; num=length(sum_types))
    b = map((s, t) -> var(s, t), sum_index_symbols, content(sum_types))

    za = call(z, a...)

    kb = call(k, b...)
    fb = call(ov, b...)

    pct_map(z, k, pct_map(a..., pct_sum(b..., call(pbs(za, fb), za, kb))))
end

"""
Pullbacks of primitive calls

𝒫(z(i) -> z(j)) = (z, k) -> delta(i, j, k)

𝒫(z->h(z)) = 𝓅(h)

𝒫(z->h(z, x)) = 𝓅(z->h(z, x))

𝒫(z -> g(h1(z), h2(z)) = (z, k) -> 𝒫(h1)(z, ((x, y) -> 𝒫(x -> g(x, y)))(h1(z), h2(z)))
(x, y) -> 𝒫(x->g(x, y))( )

𝒫(z->h1(z))(z, 𝒫()() )

partial derivative
(p, q, k) -> ((x, y) -> 𝒫(x->g(x, y))(x, k))(p, q)
"""

function pbs(z::T, ov::PrimitiveCall) where {T<:APN}
    k = make_node(Var, :_K; type=get_type(ov))

    if T == PrimitiveCall && name(mapp(z)) == name(mapp(ov))
        return pct_map(z, k, delta(content(args(z))..., content(args(ov))..., k))
    end

    contains_name(ov, name(mapp(z))) || return pct_map(z, k, constant(0))

    #= p_s = pb(content(ff(g)), fc(g))
    pg = map((p, h) -> call(p, h, k), p_s, hz)
    #= pg = map(a->call(pullback(a, fc(g)), hz..., k), content(ff(g))) =#
    pct_map(z, k, add(map(a -> call(first(pb(z, a)), z, pg...), hz)...)) =#


    g = mapp(ov)
    hz = content(args(ov))
    if all(t -> isa(t, Var), hz)
        length(hz) == 1 && return make_node(PrimitivePullback, g)
        return make_node(PrimitivePullback, pct_map(z, call(g, hz...)))
    end

    vs = new_symbol(z, ov, k, num=length(hz))
    # (x, y)
    vs = [var(v, get_type(h)) for (h, v) in zip(hz, vs)]
    # 𝒫(x->g(x, y))
    ps = [pbs(v, call(g, vs...)) for v in vs]
    # 𝒫(x->g(x, y))(x, k)
    pg = [call(p, v, k) for (v, p) in zip(vs, ps)]

    # ((x, y) -> 𝒫(x->g(x, y))(x, k))(h1, h2)
    pv = [call(pct_map(vs..., p), hz...) for p in pg]

    pct_map(z, k, add(map(a -> call(pbs(z, a), z, pv...), hz)...))
    #= pct_map(iv, k, map(a -> call(pullback(iv, a), iv, inner_pullback), content(args(ov)))...) =#
end

"""
f(z) = g(h1(z), h2(z))
Pg = [(h1, h2)->P(h1->g(h1, h2))(h1, k), (h1, h2)->P(h2->g(h1, h2))(h2, k)]
Pf = Ph1(z, Pg(h1, h2, k)) + Ph2(z, Pg(h1, h2, k))
"""
function pbs(z::APN, ov::Call)
    g = mapp(ov)
    #= ks = map(t->var(:_K, t), content(from(get_type(g)))) =#
    k = var(:_K, get_type(ov))
    hz = content(args(ov))
    vs = new_symbol(z, ov, k, num=length(hz))
    vs = [var(v, get_type(h)) for (h, v) in zip(hz, vs)]
    #= p_s = T == Call ? pb(content(ff(g))..., fc(g)) :
          map(v -> make_node(PrimitivePullback,
            length(vs) == 1 ? g : pct_map(v, call(g, vs...))
        ), vs) =#
    p_s = pb(content(ff(g))..., fc(g))

    pg = map((p, h) -> call(p, h, k), p_s, hz)
    #= pg = map(a->call(pullback(a, fc(g)), hz..., k), content(ff(g))) =#
    pct_map(z, k, add(map(a -> call(pbs(z, a), z, pg...), hz)...))
end

"""
Pullback of a contraction.

𝒫(z -> sum(i, f(z, i)))
= (z, k) -> sum(i, 𝒫(z -> f(z, i))(z, k))
"""
function pbs(z::APN, ov::T) where {T<:Contraction}
    k = var(:_K, get_type(ov))
    pct_map(z, k, make_node(T, ff(ov), call(pbs(z, fc(ov)), z, k)))
end

function pbs(z::Var, ov::Monomial)
    k = var(:_K, get_type(ov))
    ph = pbs(z, base(ov))
    contains_name(power(ov), name(z)) && error("x^x is not supported")
    pg = mul(power(ov), conjugate(monomial(base(ov), add(power(ov), constant(-1)))), k)
    pct_map(z, k, call(ph, z, pg))
end


#= """
Default to reducing static multivariate input first
"""
function pbev(zs::PCTVector, ovs::PCTVector)
    return invoke(pbev, Tuple{PCTVector, APN}, zs, ovs) 
end
 =#


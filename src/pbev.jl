export reduce_pullback, pbev

function reduce_pullback(n::APN)
    set_content(n, vcat(map(reduce_pullback, content(n))...)...)
end

function reduce_pullback(p::Pullback)
    mapp = fc(p)
    if length(ff(mapp)) == 1
        pbev(first(ff(mapp)), fc(mapp))
    else
        pbev(ff(mapp), fc(mapp))
    end
end

reduce_pullback(t::TerminalNode) = t

struct StaticMultivariate end
struct StaticVectorValued end
struct DynamicMultivariate end
struct DynamicVectorValued end
struct UnivariateChain end
struct Univariate end
struct PartialExtraction end

"""
This is a temporary solution before `Contraction` 
is redesigned to have a map inside.
"""
gc(n::APN) = fc(n)
gc(s::T) where {T<:Union{Contraction,Prod}} = pct_map(content(ff(s))..., fc(s))
gc(d::T) where {T<:AbstractDelta} = [content(upper(d))..., content(lower(d))..., fc(d)]


function pbev(z::T, ov::APN) where {T<: Union{Var, PrimitiveCall, PCTVector}}
    isa(z, PCTVector) && return pbev(StaticMultivariate, z, ov)
    isa(ov, PCTVector) && return pbev(StaticVectorValued, z, ov)
    isa(get_type(z), MapType) && return pbev(DynamicMultivariate, z, ov)
    isa(get_type(ov), MapType) && return pbev(DynamicVectorValued, z, ov)
    return pbev(Univariate, z, ov)
end



"""
Static multivariate maps

𝒫((z₁, z₂) -> expr) = ((z₁, z₂), k) -> (𝒫(z₁ -> expr)(z₁, k), 𝒫(z₂ -> expr)(z₂, k))
"""

function pbev(::Type{StaticMultivariate}, zs::PCTVector, expr::APN)
    k = var(:_K, get_type(expr))
    output = map(zs) do z
        evaluate(call(pbev(z, expr), (z, k)))
    end
    return pct_map(zs, k, output)
end

"""
Static vector valued maps

𝒫(z -> (expr₁, expr₂)) = (z, (k₁, k₂)) -> 𝒫(z -> expr₁)(z, k₁) + 𝒫(z -> expr₂)(z, k₂)
"""
function pbev(::Type{StaticVectorValued}, z::APN, exprs::PCTVector)
    ks = [var(Symbol(string("_K"), i)) for i in 1:length(exprs)]
    output = add(map((ov, k) -> evaluate(call(pbev(z, ov), z, k)), content(exprs), ks)...)
    return pct_map(z, pct_vec(ks...), output)
end



"""
Dynamic multivariate maps

𝒫(z -> expr) = (z, k) -> (a) -> 𝒫(z(a) -> expr)(z(a), k)
"""
function pbev(::Type{DynamicMultivariate}, z::APN, expr::APN)
    k = var(:_K, get_type(expr))
    t = get_type(z)
    a_symbols = new_symbol(z, expr, num=length(from(t)))
    as = [var(a, d) for (a, d) in zip(a_symbols, content(from(t)))]
    za = call(z, as...)
    output = pct_map(as..., evaluate(call(pbev(za, expr), za, k)))
    return pct_map(z, k, output)
end

"""
Dynamic vector-value maps

𝒫(z -> expr) = (z, k) -> ∑(b, 𝒫(z -> expr(b))(z, k(b)))
"""
function pbev(::Type{DynamicVectorValued}, z::APN, expr::APN)
    t = get_type(expr)
    k = var(:_K, t)
    b_symbols = new_symbol(z, expr, num=length(from(t)))
    bs = [var(b, d) for (b, d) in zip(b_symbols, content(from(t)))]

    output = pct_sum(bs..., evaluate(call(pbev(z, evaluate(call(expr, bs...))), z, call(k, bs...))))
    return pct_map(z, k, output)
end

"""
Univariate chain rule

𝒫(z -> g(expr₁, expr₂)) = (z, k) -> 𝒫(z -> (expr₁, expr₂))(z, 𝒫(g)((expr₁, expr₂), k))
"""
function pbev(::Type{UnivariateChain}, z::APN, expr::G) where {G<:APN}
    k = var(:_K, get_type(expr))
    # 𝒫(g)(expr₁, expr₂, k)
    pg = pbev(G, gc(expr), k)

    return pct_map(z, k, evaluate(call(pbev(z, gc(expr)), z, pg)))
end

function pbev(::Type{UnivariateChain}, z::APN, expr::T) where {T<:AbstractCall}
    k = var(:_K, get_type(expr))
    # 𝒫(g)(expr₁, expr₂, k)
    g = mapp(expr)
    expr = args(expr)
    pg = pbev(g, expr, k)

    return pct_map(z, k, evaluate(call(pbev(z, expr), z, pg)))
end

"""
Univariate call dispatcher.
"""
function pbev(::Type{Univariate}, z::T, expr::AbstractCall) where {T<:APN}

    k = make_node(Var, :_K; type=get_type(expr))
    if T == PrimitiveCall && mapp(z) == mapp(expr)
        return pct_map(z, k, delta(args(z), args(expr), k))
    end

    v = T == PrimitiveCall ? mapp(z) : z

    if v in free_variables(args(expr))
        return pbev(UnivariateChain, z, expr)
    elseif v in free_variables(mapp(expr))
        return pbev(PartialExtraction, z, expr)
    else
        return pct_map(z, k, constant(0))
    end
end

"""
Apply the chain rule if the output expr is not a call.
"""
function pbev(::Type{Univariate}, z::APN, expr::APN)
    pbev(UnivariateChain, z, expr)
end

"""
𝒫(z->x) = (z, k) 
    -> k if x == z
    -> 0 otherwise
"""
function pbev(::Type{Univariate}, z::Var, expr::Var)
    k = var(:_K, get_type(expr))
    if z == expr
        return pct_map(z, k, k)
    else
        return pct_map(z, k, constant(0))
    end
end

function pbev(::Type{Univariate}, z::APN, expr::Constant)
    k = var(:_K, get_type(expr))
    return pct_map(z, k, constant(0))
end

"""
Dynamic partial extraction

𝒫(z -> f(expr)(b)) = (z, k) -> 𝒫(z -> expr)(z, 𝒫(f)(expr, c -> δ(b, c, k(c))))
"""
function pbev(::Type{PartialExtraction}, z::T, expr::AbstractCall) where {T<:APN}

    k = var(:_K, get_type(expr))
    bs = content(args(expr))

    expr = fc(mapp(expr))

    c_symbols = new_symbol(z, expr, num=length(bs))
    cs = [var(s, d) for (s, d) in zip(c_symbols, get_type.(bs))]
    extractor = pct_map(cs..., delta(pct_vec(cs...), pct_vec(bs...), call(k, cs...)))

    f = isa(mapp(expr), AbstractCall) ? mapp(mapp(expr)) : f = typeof(mapp(expr))
    return pct_map(z, k, evaluate(call(pbev(z, expr), z, pbev(f, expr, extractor))))
end


"""
𝒫(') = (z, k) -> k'
"""
function pbev(::Type{Conjugate}, z::APN, k::APN)
    conjugate(k)
end

"""
𝒫(+) = ((z₁, z₂ , …, zₙ), k) -> (k, k, …, k)
"""
function pbev(::Type{Add}, zs::PCTVector, k::APN)
    pct_vec(fill(k, length(zs))...)
end

"""
𝒫(*) = ((z₁, z₂, …, zₙ), k) -> (z₂*z₃*…*zₙ + z₁*z₃*…*zₙ, … )' * k 
"""
function pbev(::Type{Mul}, zs::PCTVector, k::APN)
    products = [mul(content(remove_i(zs, i))...) for i in 1:length(zs)]
    return pct_vec([mul(conjugate(p), k) for p in products]...)
end

"""
𝒫(Sum) = ((i, j)->A(i,j), k) -> (i, j) -> k
"""
function pbev(::Type{Sum}, m::Map, k::APN)
    return pct_map(content(ff(m))..., k)
end


"""
𝒫(δ) = ((i, j, c), k) -> δ(i, j, k)
"""
function pbev(::Type{Delta}, args::PCTVector, k::APN)
    n = length(args)
    upper = content(args)[1:n÷2]
    lower = content(args)[n÷2+1:n-1]
    #= inner = content(args)[end] =#
    return delta(upper, lower, k)
end

pbev(g::Var) = make_node(PrimitivePullback, g)


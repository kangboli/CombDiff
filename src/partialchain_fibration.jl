export decompose, PComp, as_map, pp, pfuncs

abstract type AbstractBuiltinFunction end
const ABF = AbstractBuiltinFunction
ecall(ts::Vararg{APN}) = eval_all(call(ts...))


abstract type AbstractFibration <: ABF end


param(b::ABF) = b.param

maptype(b::ABF) = b.maptype

input_type(b::ABF) = from(maptype(b))

output_type(b::ABF) = content(maptype(b))

z_vars(b::ABF) = map(var, new_symbol(apns(b)...; num=length(input_type(b)), symbol=:_z), content(input_type(b)))

function zk_vars(b::ABF)
    its = input_type(b)
    ots = v_wrap(output_type(b))
    #= symbols = new_symbol(apns(b)...; num=length(ots) + length(its)) =#
    #= zs = map(var, symbols[1:length(its)], its)
    ks = map(var, symbols[length(its)+1:end], ots) =#

    zs = map(var, new_symbol(apns(b)...; num=length(its), symbol=:_z), its)
    ks = map(var, new_symbol(apns(b)...; num=length(ots), symbol=:_k), ots)
    return zs, ks
end
apns(b::ABF) = apns(param(b))
apns(b::APN) = [v_wrap(b)...] 
apns(::Nothing) = [] 


"""
The identity map
"""

function decompose(z::Var, ov::Var)
    z == ov && return comp(z)
    return comp(z, Pconst(ov, MapType(v_wrap(get_type(z)), get_type(ov))))
end


# The identity map is represented as an empty composition.

"""
The map to a constant
"""

struct Pconst <: ABF
    param::APN
    maptype::MapType
end

function as_map(b::Pconst)
    return pct_map(z_vars(b)..., param(b))
end

decompose(z::APN, c::Constant) = comp(z, Pconst(c, MapType(v_wrap(get_type(z)), get_type(c))))

function pp(b::Pconst)
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., constant(0))
end

pretty(b::Pconst) = "->$(pretty(param(b)))"

"""
Complex Conjugate
"""

struct BConj <: ABF end
param(::BConj) = nothing
maptype(::BConj) = MapType(VecType([C()]), C())

decompose(z::APN, c::Conjugate) = push(decompose(z, fc(c)), BConj())

function as_map(b::BConj, zs=z_vars(b))
    pct_map(zs..., conjugate(zs...))
end

function pp(b::BConj, (zs, ks)=zk_vars(b))
    pct_map(zs..., ks..., conjugate(ks...))
end

pretty(b::BConj) = "†"

"""
Add by a value
"""

struct BAdd <: ABF
    param::APN
    maptype::MapType
end

function decompose(zs::APN, ov::Add)
    target, rest = avoid_overflow(zs, ov)
    ptype = MapType(v_wrap(get_type(target)), get_type(ov))
    push(decompose(zs, target), BAdd(add(content(rest)...), ptype))
end

function avoid_overflow(zs::APN, ov::APN)
    contains_zs(t) = any(z -> contains_name(t, name(z)), v_wrap(zs))
    i = findfirst(contains_zs, content(fc(ov)))
    i === nothing && (i = 1)
    target, rest = fc(ov)[i], fc(ov)[1:end.!=i]
    return target, rest
end

function as_map(b::BAdd, zs=z_vars(b))
    pct_map(zs..., add(zs..., param(b)))
end

function pp(b::BAdd)
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., v_unwrap(ks))
end

pretty(b::BAdd) = "+$(pretty(param(b)))"

"""
Multiply by a value
"""
struct BMul <: ABF
    param::APN
    maptype::MapType
end

param(b::BMul) = b.param

function decompose(zs::APN, ov::Mul)
    target, rest = avoid_overflow(zs, ov)
    ptype = MapType(v_wrap(get_type(target)), get_type(ov))
    push(decompose(zs, target), BMul(mul(content(rest)...), ptype))
end

function as_map(b::BMul, zs=z_vars(b))
    pct_map(zs..., mul(zs..., param(b)))
end

function pp(b::BMul)
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., mul(conjugate(param(b)), ks...))
end

pretty(b::BMul) = "*$(pretty(param(b)))"

"""
Raise to a variable power.
"""
struct BMon <: ABF
    param::APN
    maptype::MapType
end
param(b::BMon) = b.param

function decompose(z::APN, ov::Monomial)
    push(decompose(z, base(ov)), BMon(power(ov), MapType(v_wrap(get_type(base(ov))), get_type(ov))))
end

function as_map(b::BMon, zs=z_vars(b))
    pct_map(zs..., monomial(zs..., param(b)))
end

function pp(b::BMon)
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., mul(param(b), conjugate(monomial(zs..., add(param(b), constant(-1)))), ks...))
end

pretty(b::BMon) = "^$(pretty(param(b)))"

"""
Summation
"""
struct BSum <: ABF
    param::PCTVector
    maptype::MapType
end

param(b::BSum) = b.param
maptype(b::BSum) = b.maptype


function decompose(z::APN, ov::Sum)
    inner_map = pct_map(content(ff(ov))..., fc(ov))
    push(decompose(z, inner_map), BSum(ff(ov), MapType(v_wrap(get_type(inner_map)), get_type(ov))))
end

function as_map(b::BSum)
    zs = z_vars(b)
    pct_map(zs..., pct_sum(param(b)..., call(zs..., param(b)...)))
end

function pp(b::BSum)
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., pct_map(param(b)..., ks...))
end

pretty(b::BSum) = "∑$(join(pretty.(param(b))))"

"""
Exponentiation
"""
struct BExp <: ABF end

function decompose(z::APN, ov::Exp)
    push(decompose(z, fc(ov)), BExp())
end

function as_map(::BExp)
    error("Not yet supported")
end

function pp(::BExp)
    error("Not yet supported")
end

"""
z -> f1(f2(z))
f1 and f2 can depend on z themselves
Todo: make the right-most functions applied first.
"""
struct PComp <: ABF
    input::PCTVector
    pfuncs::Vector{ABF}
    maptype::MapType
end

const Seg = Union{ABF,AbstractFibration}
comp(z::APN, f::Vararg{Seg}) = PComp(v_wrap(z), [f...], MapType(v_wrap(get_type(z)), output_type(last(f))))
comp(z::APN) = PComp(v_wrap(z), [], MapType(v_wrap(get_type(z)), get_type(z)))
#= comp(z::Var, f::Vararg{Seg}) = PComp(pct_vec(z), [f...], MapType(get_type(z), output_type(last(f)))) =#


input(c::PComp) = c.input
pfuncs(c::PComp) = c.pfuncs
param(c::PComp) = (input(c), pfuncs(c))

push(c::PComp, f::Vararg) = comp(input(c), pfuncs(c)..., f...)

pop(c::PComp) = last(pfuncs(c)), comp(input(c), pfuncs(c)[1:end-1]...)

Base.isempty(c::PComp) = isempty(pfuncs(c))
#= output_type(c::PComposition) = get_type(call(as_map(c), input(c))) =#

pretty(c::PComp) = "$(pretty(input(c))): " * join([pretty.(reverse(pfuncs(c)))...], " ▷ ")
Base.show(io::IO, c::PComp) = println(io, pretty(c))

apns(fc::PComp) = vcat(content(input(fc)), apns.(pfuncs(fc))...)

function as_map(c::PComp)
    result = foldl((r, f)->ecall(as_map(f), v_wrap(r)...), pfuncs(c); init=input(c))
    #= result = input(c)
    for f in pfuncs(c)
        println(pretty(as_map(f)))
        result = evaluate(call(as_map(f), v_wrap(result)...))
    end =#
    return pct_map(content(input(c))..., result)
end

function pp(c::PComp)
    zs = input(c)
    #= ot = v_wrap(output_type(c)) =#
    #= ks = pct_vec([var(Symbol("_k_$(i)"), t) for (i, t) in enumerate(ot)]...) =#
    ys, ks = zk_vars(c)
    isempty(pfuncs(c)) && return pct_map(ys..., ks..., v_unwrap(ks))

    f, x_expr = pop(c)
    expr = v_wrap(eval_all(call(as_map(x_expr), zs...)))
    #= p_f = pp(f)
    chain = v_wrap(eval_all(call(p_f, expr..., ks...)))
    p_expr = pp(x_expr)
    p_call = call(p_expr, zs..., chain...)
    chain = v_wrap(eval_all(p_call)) =#
    chain = v_wrap(ecall(pp(x_expr), ys..., v_wrap(ecall(pp(f), expr..., ks...))...))
    f_map = as_map(f)
    if any(s -> contains_name(f_map, s), name.(zs))
        is = map(var, new_symbol(expr, ys..., ks...; num=length(expr), symbol=:_i), v_wrap(get_type(expr)))
        #= deltas = ks
        for (e, i) in zip(expr, is)
            deltas = map(d -> delta(e, i, d), deltas)
        end =#
        deltas = foldl((ds, (e, i)) -> map(d->delta(e, i, d), ds), zip(content(expr), is); init=ks)
        #= println(">>>>>>")
        println(pretty(expr))
        println.(pretty.(deltas)) =#
        #= deltas = reduce((e_i, d)->delta(first(e_i), last(e_i), d), zip(expr, is); init=k) =#
        partial = v_wrap(ecall(pp(decompose(zs, f_map)), ys..., pct_map(is..., v_unwrap(deltas))))
        chain = pct_vec(map(add, chain, partial)...)
        #= println(pretty(partial))
        println()
        println(pretty(chain))
        println("<<<<<<") =#
    end
    return pct_map(ys..., ks..., v_unwrap(chain))
end


"""
Fibration represents: z -> f
as b -> z -> f(z)(b)
b: fiber_var
z -> f(z)(b): fibers
input_type: type of z
maptype: type of f(z)
"""
struct Fibration <: AbstractFibration
    fiber_var::PCTVector
    fibers::PComp
    maptype::MapType
end

fiber_var(f::Fibration) = f.fiber_var
fibers(f::AbstractFibration) = f.fibers
param(f::Fibration) = (f.fiber_var, f.fibers)


# b -> z -> f(z)(b) => z -> b -> (z -> f(z)(b))(z)
# => z -> b -> f(z)(b) => z -> f(z)
function as_map(fib::Fibration, zs=z_vars(fib))
    b_fb = as_map(fibers(fib))
    pct_map(zs..., pct_map(fiber_var(fib)..., evaluate(call(b_fb, zs...))))
end


# Decompose a map-valued map into fibers
# z -> f(z) => b -> z -> f(z)(b)
# z -> f(z)(b) is then decomposed.
function decompose(z::APN, ov::Map)
    bs, fb = ff(ov), fc(ov)
    comp(z, Fibration(bs, decompose(z, fb), MapType(v_wrap(get_type(z)), get_type(ov))))
end

function pp(fib::Fibration)
    bs = fiber_var(fib)
    #= vectype = input_type(fib)
    symbols = new_symbol(apns(fib)..., num=length(vectype) + 1) =#
    #= zs = [var(s, t) for (s, t) in zip(symbols[1:end-1], vectype)]

    k = var(last(symbols), output_type(fib)) =#
    zs, ks = zk_vars(fib)
    return pct_map(zs..., ks..., pct_sum(bs..., call(pp(fibers(fib)), zs..., call(ks..., bs...))))
end

function apns(fib::Fibration)
    return [fiber_var(fib)..., apns(fibers(fib))...]
end

function pretty(fib::Fibration)
    return "{$(pretty(fiber_var(fib))) ⇥ $(pretty(fibers(fib)))}"
end

"""
Finite fibration
1 -> z -> f(z)(1)
z -> [f(z)(1), …, f(z)(4)]: fibers
"""
struct FiniteFibration <: AbstractFibration
    fibers::Vector{PComp}
    maptype::MapType
end

function as_map(fib::FiniteFibration, zs=z_vars(fib))
    b_fb = as_map.(fibers(fib))
    pct_map(zs..., pct_vec([ecall(f, zs...) for f in b_fb]...))
end

function decompose(z::APN, ov::PCTVector)
    comp(z, FiniteFibration([decompose(z, t) for t in ov], MapType(v_wrap(get_type(z)), get_type(ov))))
end

"""
𝒫(z -> expr1, expr2) = (z, k1, k2) -> 𝒫(z -> expr1)(z, k1) + 𝒫(z -> expr2)(z, k2)
"""
function pp(fib::FiniteFibration)
    zs, ks = zk_vars(fib)
    return pct_map(zs..., ks..., add(
        [ecall(pp(f), zs..., k) for (f, k) in zip(fibers(fib), ks)]...))
end

apns(fib::FiniteFibration) = vcat(apns.(fibers(fib))...)

function pretty(fib::FiniteFibration)
    return join(pretty.(fibers(fib)), "|")
end

"""
Map to a call
"""
struct BMap <: ABF
    param::APN
    maptype::MapType
end
param(b::BMap) = b.param

function as_map(m::BMap)
    return param(m)
end

function decompose(z::APN, ov::AbstractCall)
    length(args(ov)) == 1 && return push(decompose(z, first(args(ov))), BMap(mapp(ov), get_type(mapp(ov))))
    push(decompose(z, args(ov)), BMap(mapp(ov)))
end

function decompose(zs::PCTVector, ov::Var)
    length(zs) == 1 && return decompose(first(zs), ov)
    const_type = MapType(get_type(zs), get_type(ov))
    i = findfirst(t -> t == ov, content(zs))
    i === nothing && return comp(zs, Pconst(ov, const_type))
    return comp(zs, Pconst(constant(i), MapType(get_type(zs), I())), BMap(zs, MapType(v_wrap(I()), get_type(first(zs)))))
end

function pp(b::BMap)
    isa(param(b), Map) && return pp(decompose(param(b)))
    isa(param(b), Union{Var,PCTVector}) && return pullback(param(b))
end

function decompose(map::Map)
    result = [decompose(t, fc(map)) for t in content(ff(map))]
    length(result) == 1 && return first(result)
end

function pretty(b::BMap)
    return "ℳ $(pretty(param(b)))"
end

v_wrap(n::APN) = pct_vec(n)
v_wrap(n::T) where {T<:Union{ElementType,MapType}} = VecType([n])
v_wrap(n::T) where {T<:Union{PCTVector,VecType}} = n
v_unwrap(n::Union{PCTVector,Vector}) = length(n) == 1 ? first(n) : n
v_unwrap(n::APN) = n


#
#= if length(functions(c)) == 1
    return pct_map(zs..., k, call(pp(first(functions(c))), zs..., k)) 

end =#

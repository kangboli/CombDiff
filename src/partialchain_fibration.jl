# The types in this module is for documentation instead of performance purposes.
# Do not optimize this code because it is not the bottleneck and is already difficult 
# to debug.
export decompose, PComp, as_map, pp, pfuncs

"""
An abstract interface for functions. A function needs to implement

    * `maptype` or (`input_type` and `output_type`).
    * one of 
        * `param`: the parametrization of the function.
            For instance, `v -> v * x` is parametrized by x.
        * or `apns`: the abstract pct nodes involved in the function.
            The purpose of this is to avoid bounding the 
            variables involved in those nodes when creating 
            the `z` and `k` variables. This can be derived from `param`.
    * `decompose`: recursively construct a `PComp` from an input variable `zs`
        and a pct node. This can be considered the constructor of functions from
        ASTs.
    * `as_map`: convert the function to a pct map so that it can be applied.
        This is necessary because it is not clear how to apply a function in its 
        abstract form.
    * `pp`: construct the pullback of the function as a pct map.
"""
abstract type AbstractBuiltinFunction end
const ABF = AbstractBuiltinFunction
ecall(ts::Vararg{APN}) = eval_all(call(ts...))

abstract type AbstractFibration <: ABF end

"""
    param(b::ABF)

Gives the parametriztion of a function if it is parametric. 
Otherwise returns nothing. For example, 
`v -> v * x` is parametrized with `x`.
"""
param(b::ABF)::APN = b.param

"""
    maptype(b::ABF)

Gives the maptype of the function, from which 
the input and output types can be obtained.
"""
maptype(b::ABF)::MapType = b.maptype

input_type(b::ABF)::VecType = from(maptype(b))

output_type(b::ABF)::AbstractPCTType = content(maptype(b))

z_vars(b::ABF)::Vector{T} where {T<:Var} = map(var,
    new_symbol(apns(b)...; num=length(input_type(b)), symbol=:_z), content(input_type(b)))

"""
    zk_vars(b::ABF)

Make the variables that represents the z and k in 𝒫(f) = (zs, ks) -> ...
zs and ks are vectors because the function can have multiple inputs and 
outputs. 
"""
function zk_vars(b::ABF)
    its = input_type(b)
    ots = v_wrap(output_type(b))
    zs = map(var, new_symbol(apns(b)...; num=length(its), symbol=:_z), its)
    ks = map(var, new_symbol(apns(b)...; num=length(ots), symbol=:_k), ots)
    return zs, ks
end

apns(b::ABF)::Vector{APN} = apns(param(b))
apns(b::APN)::Vector{APN} = [v_wrap(b)...]
apns(::Nothing)::Vector{APN} = []


"""
The identity map
"""

function decompose(z::Var, ov::Var)::PComp
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

as_map(b::Pconst)::Map = pct_map(z_vars(b)..., param(b))

decompose(z::APN, c::Constant)::PComp = comp(z, Pconst(c, MapType(v_wrap(get_type(z)), get_type(c))))

function pp(b::Pconst)::Map
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., constant(0))
end

pretty(b::Pconst) = "->$(pretty(param(b)))"

"""
Complex Conjugate
"""

struct BConj <: ABF end
param(::BConj)::Nothing = nothing
maptype(::BConj)::MapType = MapType(VecType([C()]), C())

decompose(z::APN, c::Conjugate)::PComp = push(decompose(z, fc(c)), BConj())

as_map(b::BConj, zs=z_vars(b))::Map = pct_map(zs..., conjugate(zs...))

function pp(b::BConj, (zs, ks)=zk_vars(b))::Map
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

function decompose(zs::APN, ov::Add)::PComp
    target, rest = avoid_overflow(zs, ov)
    ptype = MapType(v_wrap(get_type(target)), get_type(ov))
    push(decompose(zs, target), BAdd(add(content(rest)...), ptype))
end

function avoid_overflow(zs::APN, ov::APN)::Tuple{APN,PCTVector}
    contains_zs(t) = any(z -> contains_name(t, name(z)), v_wrap(zs))
    i = findfirst(contains_zs, content(fc(ov)))
    i === nothing && (i = 1)
    target, rest = fc(ov)[i], fc(ov)[1:end.!=i]
    return target, rest
end

as_map(b::BAdd, zs=z_vars(b))::Map = pct_map(zs..., add(zs..., param(b)))

function pp(b::BAdd)::Map
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

param(b::BMul)::APN = b.param

function decompose(zs::APN, ov::Mul)::PComp
    target, rest = avoid_overflow(zs, ov)
    ptype = MapType(v_wrap(get_type(target)), get_type(ov))
    push(decompose(zs, target), BMul(mul(content(rest)...), ptype))
end

function as_map(b::BMul, zs=z_vars(b))::Map
    pct_map(zs..., mul(zs..., param(b)))
end

function pp(b::BMul)::Map
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
param(b::BMon)::APN = b.param

function decompose(z::APN, ov::Monomial)::PComp
    push(decompose(z, base(ov)), BMon(power(ov), MapType(v_wrap(get_type(base(ov))), get_type(ov))))
end

function as_map(b::BMon, zs=z_vars(b))::Map
    pct_map(zs..., monomial(zs..., param(b)))
end

function pp(b::BMon)::Map
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

param(b::BSum)::PCTVector = b.param
maptype(b::BSum)::MapType = b.maptype


function decompose(z::APN, ov::Sum)::PComp
    inner_map = pct_map(content(ff(ov))..., fc(ov))
    push(decompose(z, inner_map), BSum(ff(ov), MapType(v_wrap(get_type(inner_map)), get_type(ov))))
end

function as_map(b::BSum, zs=z_vars(b))::Map
    pct_map(zs..., pct_sum(param(b)..., call(zs..., param(b)...)))
end

function pp(b::BSum)::Map
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., pct_map(param(b)..., ks...))
end

pretty(b::BSum) = "∑$(join(pretty.(param(b))))"

"""
Exponentiation
"""
struct BExp <: ABF end

decompose(z::APN, ov::Exp)::PComp = push(decompose(z, fc(ov)), BExp())

as_map(::BExp) = error("Not yet supported")

pp(::BExp) = error("Not yet supported")

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
function comp(z::T, f::Vararg{Seg})::PComp where T <: APN
    T == PCTVector && length(z) > 1 && error("multiple inputs shouldn't enter pcomp")
    PComp(v_wrap(z), [f...], MapType(v_wrap(get_type(z)), output_type(last(f))))
end
function comp(z::T)::PComp where T <: APN
    T == PCTVector && length(z) > 1 && error("multiple inputs shouldn't enter pcomp")
    PComp(v_wrap(z), [], MapType(v_wrap(get_type(z)), get_type(z)))
end

input(c::PComp)::PCTVector = c.input
pfuncs(c::PComp)::Vector{ABF} = c.pfuncs
#= param(c::PComp) = (input(c), pfuncs(c)) =#

push(c::PComp, f::Vararg)::PComp = comp(input(c), pfuncs(c)..., f...)

pop(c::PComp)::Tuple{T, PComp} where T <: ABF = last(pfuncs(c)), comp(input(c), pfuncs(c)[1:end-1]...)

Base.isempty(c::PComp)::Bool = isempty(pfuncs(c))

pretty(c::PComp) = "$(pretty(input(c))): " * join([pretty.(reverse(pfuncs(c)))...], " ◀ ")
Base.show(io::IO, c::PComp) = println(io, pretty(c))

apns(fc::PComp)::Vector{APN} = vcat(content(input(fc)), apns.(pfuncs(fc))...)

function as_map(c::PComp)::Map
    result = foldl((r, f) -> ecall(as_map(f), v_wrap(r)...), pfuncs(c); init=input(c))
    return pct_map(content(input(c))..., result)
end

#= result = input(c)
for f in pfuncs(c)
    println(pretty(as_map(f)))
    result = evaluate(call(as_map(f), v_wrap(result)...))
end =#

function pp(c::PComp)::Map
    zs = input(c)
    ys, ks = zk_vars(c)
    # one can use either zs or ys.
    ys = zs

    isempty(pfuncs(c)) && return pct_map(ys..., ks..., v_unwrap(pct_vec(ks...)))

    f, x_expr = pop(c)
    expr = v_wrap(ecall(as_map(x_expr), ys...))
    p_expr = pp(x_expr)
    p_f = pp(f)
    #= p_f = pp(f)
    chain = v_wrap(eval_all(call(p_f, expr..., ks...)))
    p_expr = pp(x_expr)
    p_call = call(p_expr, zs..., chain...)
    chain = v_wrap(eval_all(p_call)) =#
    chain = v_wrap(ecall(p_expr, ys..., v_wrap(ecall(p_f, expr..., ks...))...))
    f_map = as_map(f)
    if any(s -> contains_name(f_map, s), name.(zs))
        is = map(var, new_symbol(expr, ys..., ks...; num=length(expr), symbol=:_d), v_wrap(get_type(expr)))
        #= deltas = ks
        for (e, i) in zip(expr, is)
            deltas = map(d -> delta(e, i, d), deltas)
        end =#
        deltas = foldl((ds, (e, i)) -> map(d -> delta(e, i, d), ds), zip(content(expr), is); init=ks)
        partial = v_wrap(ecall(pp(decompose(zs, f_map)), ys..., pct_map(is..., v_unwrap(deltas))))
        chain = pct_vec(map(add, chain, partial)...)
    end
    result = pct_map(ys..., ks..., v_unwrap(chain))
    return result
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

fiber_var(f::Fibration)::PCTVector = f.fiber_var
fibers(f::AbstractFibration) = f.fibers
#= param(f::Fibration) = (f.fiber_var, f.fibers) =#


# b -> z -> f(z)(b) => z -> b -> (z -> f(z)(b))(z)
# => z -> b -> f(z)(b) => z -> f(z)
function as_map(fib::Fibration, zs=z_vars(fib))::Map
    b_fb = as_map(fibers(fib))
    pct_map(zs..., pct_map(fiber_var(fib)..., evaluate(call(b_fb, zs...))))
end


# Decompose a map-valued map into fibers
# z -> f(z) => b -> z -> f(z)(b)
# z -> f(z)(b) is then decomposed.
function decompose(z::APN, ov::Map)::PComp
    bs, fb = ff(ov), fc(ov)
    comp(z, Fibration(bs, decompose(z, fb), MapType(v_wrap(get_type(z)), get_type(ov))))
end

function pp(fib::Fibration)::Map
    bs = fiber_var(fib)
    zs, ks = zk_vars(fib)
    return pct_map(zs..., ks..., pct_sum(bs..., call(pp(fibers(fib)), zs..., call(ks..., bs...))))
end

apns(fib::Fibration)::Vector{APN} = [fiber_var(fib)..., apns(fibers(fib))...]

pretty(fib::Fibration) = "{$(pretty(fiber_var(fib))) ⇥ $(pretty(fibers(fib)))}"

"""
Finite fibration
1 -> z -> f(z)(1)
z -> [f(z)(1), …, f(z)(4)]: fibers
"""
struct FiniteFibration <: AbstractFibration
    fibers::Vector{PComp}
    maptype::MapType
end

function as_map(fib::FiniteFibration, zs=z_vars(fib))::Map
    b_fb = as_map.(fibers(fib))
    pct_map(zs..., pct_vec([ecall(f, zs...) for f in b_fb]...))
end

function decompose(z::APN, ov::PCTVector)::PComp
    comp(z, FiniteFibration([decompose(z, t) for t in ov], MapType(v_wrap(get_type(z)), get_type(ov))))
end

"""
𝒫(z -> expr1, expr2) = (z, k1, k2) -> 𝒫(z -> expr1)(z, k1) + 𝒫(z -> expr2)(z, k2)
"""
function pp(fib::FiniteFibration)::Map
    zs, ks = zk_vars(fib)
    return pct_map(zs..., ks..., add(map((f, k) -> ecall(pp(f), zs..., k), fibers(fib), ks)...))
end

apns(fib::FiniteFibration)::Vector{APN} = vcat(apns.(fibers(fib))...)

pretty(fib::FiniteFibration) = join(pretty.(fibers(fib)), "|")

"""
Map to a call
"""
struct BMap <: ABF
    param::APN
end
param(b::BMap)::APN = b.param
function maptype(b::BMap)::MapType
    result = get_type(param(b))
    isa(result, VecType) && return MapType(VecType([I()]), first(content(result)))
    return result
end

as_map(m::BMap)::APN = param(m)

function decompose(z::APN, ov::AbstractCall)::PComp
    length(args(ov)) == 1 && return push(decompose(z, first(args(ov))), BMap(mapp(ov)))
    push(decompose(z, args(ov)), BMap(mapp(ov)))
end

function decompose(zs::PCTVector, ov::Var)::PComp
    length(zs) == 1 && return decompose(first(zs), ov)
    const_type = MapType(get_type(zs), get_type(ov))
    i = findfirst(t -> t == ov, content(zs))
    i === nothing && return comp(zs, Pconst(ov, const_type))
    return comp(zs, Pconst(constant(i), MapType(get_type(zs), Z())), BMap(zs))
end

function pp(b::BMap)::AbstractMap
    m = param(b)
    process_param(p::Map) = pp(decompose(p))
    # TODO: Implement the vector case.
    process_param(p::APN) = primitive_pullback(p)
    #= process_param(p::PrimitiveCall) = pp(decompose(p)) =#
    function process_param(p::Var)
        from_types = content(from(get_type(m)))
        n_args = length(from_types)
        zs, ks = zk_vars(b)
        if n_args == 1 
            linear(get_type(m)) || return pullback(p)
            return pct_map(zs..., ks..., call(conjugate(m), ks...)) 
        end
        #= new_from = map(var, new_symbol(m, zs..., ks..., num=n_args), from_types) =#
        pullbacks = map(z->call(primitive_pullback(pct_map(z, call(m, zs...))), z, ks...), zs)
        pct_map(zs..., ks..., pct_vec(pullbacks...))
    end
    return process_param(m)
end

#= decompose(map::Map)::Union{PComp, Vector{PComp}} = v_unwrap([decompose(t, fc(map)) for t in content(ff(map))]) =#
decompose(map::Map)::Union{PComp, Vector{PComp}} = decompose(ff(map), fc(map))

pretty(b::BMap) = return "ℳ $(pretty(param(b)))"

v_wrap(n::APN)::PCTVector = pct_vec(n)
v_wrap(n::T) where {T<:Union{ElementType,MapType}} = VecType([n])
v_wrap(n::T) where {T<:Union{PCTVector,VecType}} = n
v_unwrap(n::Union{PCTVector, Vector}) = length(n) == 1 ? first(n) : n
v_unwrap(n::APN) = n

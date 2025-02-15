# The types in this module are designed to be comprehensible instead of performance purposes.
# Do not optimize this code because it is not the bottleneck and is already difficult 
# to debug.
#
# Most functions in this file are mutually recursive, but each of the function is small and 
# possible to reason about.

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

"""
get the type of the input
"""
input_type(b::ABF)::VecType = get_bound_type(maptype(b))

"""
get the type of the output
"""
output_type(b::ABF)::AbstractPCTType = get_body_type(maptype(b))

"""
    z_vars(b::ABF)

Make the variablse that represents zs when
converting a function f to (zs) -> f(zs) in `as_map`.
"""
function z_vars(b::ABF)::Vector{<:Var}
    result = map(var, new_symbol(apns(b)...; num=length(input_type(b)), symbol=:_z), get_content_type(input_type(b)))
    isempty(result) && return Vector{Var}()
    return result
end

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

"""
Get the set of expressions captured in the ABF.
"""
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

function zero_map(::ElementType)
    return constant(0)
end

function zero_map(v::VecType)
    return pct_vec(map(zero_map, content(v))...)
end

function zero_map(t::MapType)
    bound_types = get_bound_type(t)
    new_vars = map(var, new_symbol(; num=length(bound_types)), bound_types)
    return pct_map(new_vars..., zero_map(get_body_type(t)))
end

function pp(b::Pconst)::Map
    zs, ks = zk_vars(b)
    #= @assert all(z -> isa(get_type(z), ElementType), zs) =#
    pct_map(zs..., ks..., v_unwrap(zero_map(get_type(v_unwrap(pct_vec(zs...))))))
end

pretty(b::Pconst) = "->$(pretty(param(b)))"

"""
Complex Conjugate
"""

struct BConj <: ABF end
param(::BConj)::Nothing = nothing
maptype(::BConj)::MapType = MapType(VecType([C()]), C())

decompose(z::APN, c::Conjugate)::PComp = push(decompose(z, get_body(c)), BConj())

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

"""
When decomposing addition or multiplication, one needs to do this to avoid a stackoverflow.
For example: x -> v + x = x -> (x -> x + v)(x) = x -> (x -> (x -> x + v)(x))(x) = ...
"""
function avoid_overflow(zs::APN, ov::APN)::Tuple{APN,PCTVector}
    #= contains_zs(t) = any(z -> contains_name(t, name(z)), v_wrap(zs)) =#
    contains_zs(t) = any(z -> z in get_free(t), v_wrap(zs))
    i = findfirst(contains_zs, content(get_body(ov)))
    i === nothing && (i = 1)
    target, rest = get_body(ov)[i], get_body(ov)[1:end.!=i]
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

struct BDelta <: ABF
    param::APN
    maptype::MapType
    delta_type::Type
end

function decompose(z::APN, ov::T) where {T<:AbstractDelta}
    (contains_name(upper(ov), name(v_unwrap(z))) || contains_name(lower(ov), name(v_unwrap(z)))) &&
        error("Delta divergence not yet implemented.")
    body_type = get_type(get_body(ov))
    push(decompose(z, get_body(ov)), BDelta(pct_vec(upper(ov), lower(ov)),
        MapType(v_wrap(body_type), body_type), T))
end

function as_map(d::BDelta, zs=z_vars(d))::Map
    if d.delta_type == DeltaNot
        return pct_map(zs..., make_node(d.delta_type, param(d)..., v_unwrap(zs)))
    end
end

function pp(d::BDelta)
    zs, ks = zk_vars(d)
    pct_map(zs..., ks..., make_node(d.delta_type, param(d)..., v_unwrap(ks)))
end


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
    inner_map = pct_map(content(get_bound(ov))..., get_body(ov))
    push(decompose(z, inner_map), BSum(get_bound(ov), MapType(v_wrap(get_type(inner_map)), get_type(ov))))
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
struct BExp <: ABF
    maptype::MapType
end

decompose(z::APN, ov::Exp)::PComp = push(decompose(z, get_body(ov)), BExp(
    MapType(VecType([get_type(get_body(ov))]), get_type(get_body(ov)))
))

as_map(b::BExp, zs=z_vars(b)) = pct_map(zs..., pct_exp(zs...))

function pp(b::BExp)
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., mul(conjugate(pct_exp(zs...)), ks...))
end

pretty(b::BExp) = "exp"

apns(::BExp) = []

"""
Log
"""
struct BLog <: ABF
    maptype::MapType
end

decompose(z::APN, ov::Log)::PComp = push(decompose(z, get_body(ov)), BLog(
    MapType(VecType([get_type(get_body(ov))]), get_type(get_body(ov)))
))

as_map(b::BLog, zs=z_vars(b)) = pct_map(zs..., pct_log(zs...))

function pp(b::BLog)
    zs, ks = zk_vars(b)
    pct_map(zs..., ks..., mul(conjugate(monomial(zs..., constant(-1))), ks...))
end

pretty(b::BLog) = "log"

apns(::BLog) = []


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
function comp(z::T, f::Vararg{Seg})::PComp where {T<:APN}
    T == PCTVector && length(z) > 1 && error("multiple inputs shouldn't enter pcomp")
    PComp(v_wrap(z), [f...], MapType(v_wrap(get_type(z)), output_type(last(f))))
end
function comp(z::T)::PComp where {T<:APN}
    T == PCTVector && length(z) > 1 && error("multiple inputs shouldn't enter pcomp")
    PComp(v_wrap(z), [], MapType(v_wrap(get_type(z)), get_type(z)))
end

input(c::PComp)::PCTVector = c.input
pfuncs(c::PComp)::Vector{ABF} = c.pfuncs
#= param(c::PComp) = (input(c), pfuncs(c)) =#

push(c::PComp, f::Vararg)::PComp = comp(input(c), pfuncs(c)..., f...)

pop(c::PComp)::Tuple{T,PComp} where {T<:ABF} = last(pfuncs(c)), comp(input(c), pfuncs(c)[1:end-1]...)

Base.isempty(c::PComp)::Bool = isempty(pfuncs(c))

pretty(c::PComp) = "$(pretty(input(c))): " * join([pretty.(reverse(pfuncs(c)))...], " B ") * "I"
Base.show(io::IO, c::PComp) = println(io, pretty(c))

apns(c::PComp)::Vector{APN} = vcat(content(input(c)), apns.(pfuncs(c))...)

function as_map(c::PComp)::Map
    result = input(c)
    for f in pfuncs(c)
        result = ecall(as_map(f), v_wrap(result)...)
    end
    #= result = foldl((r, f) -> ecall(as_map(f), v_wrap(r)...), pfuncs(c); init=input(c)) =#
    return pct_map(content(input(c))..., result)
end

#= result = input(c)
for f in pfuncs(c)
    println(pretty(as_map(f)))
    result = evaluate(call(as_map(f), v_wrap(result)...))
end =#

"""
This is a B-rule:

𝒫 (x -> B(f(expr))) = (x, k) -> 𝒫 (x->expr)(x, 𝒫 (f)(expr, k)) + 𝒫 (x -> f)(x, i -> δ(expr, i, k))

Be careful with touching this function. It is very hard to get this right.
"""
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
    if any(s -> s in get_free(f_map), zs)
        #= if any(s -> contains_name(f_map, s), name.(zs)) =#
        is = map(var, new_symbol(expr, ys..., ks...; num=length(expr), symbol=:_d), v_wrap(get_type(expr)))
        #= deltas = ks
        for (e, i) in zip(expr, is)
            deltas = map(d -> delta(e, i, d), deltas)
        end =#
        deltas = foldl((ds, (e, i)) -> map(d -> delta(e, i, d), ds), zip(content(expr), is); init=ks)
        partial = v_wrap(ecall(pp(decompose(zs, f_map)), ys..., pct_map(is..., v_unwrap(pct_vec(deltas...)))))
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

fiber_var(f::AbstractFibration)::PCTVector = f.fiber_var
fibers(f::AbstractFibration) = f.fibers
#= param(f::Fibration) = (f.fiber_var, f.fibers) =#


# b -> z -> f(z)(b) => z -> b -> (z -> f(z)(b))(z)
# => z -> b -> f(z)(b) => z -> f(z)
function as_map(fib::Fibration, zs=z_vars(fib))::Map
    b_fb = as_map(fibers(fib))
    pct_map(zs..., pct_map(fiber_var(fib)..., ecall(b_fb, zs...)))
end


# Decompose a map-valued map into fibers
# z -> f(z) => b -> z -> f(z)(b)
# z -> f(z)(b) is then decomposed.
function decompose(z::APN, ov::Map)::PComp
    bs, fb = get_bound(ov), get_body(ov)
    comp(z, Fibration(bs, decompose(z, fb), MapType(v_wrap(get_type(z)), get_type(ov))))
end

function pp(fib::Fibration)::Map
    bs = fiber_var(fib)
    zs, ks = zk_vars(fib)
    return pct_map(zs..., ks..., pct_sum(bs..., call(pp(fibers(fib)), zs..., splat(call(ks..., bs...)))))
end

apns(fib::Fibration)::Vector{APN} = [fiber_var(fib)..., apns(fibers(fib))...]

pretty(fib::Fibration) = "{$(pretty(fiber_var(fib))) ⇥ $(pretty(fibers(fib)))}"

struct ParametricFibration <: AbstractFibration
    type_var::PCTVector
    fiber_var::PCTVector
    fibers::PComp
    maptype::MapType
end

type_var(pf::ParametricFibration) = pf.type_var

function decompose(z::APN, ov::ParametricMap)::PComp
    type_var, m = get_bound(ov), get_body(ov)
    bs, fb = get_bound(m), get_body(m)
    comp(z, ParametricFibration(type_var, bs,
        decompose(z, fb), MapType(v_wrap(get_type(z)), get_type(m))))
end

function as_map(pf::ParametricFibration, zs=z_vars(pf))::Map
    b_fb = as_map(fibers(pf))
    pct_map(zs..., parametric_map(type_var(pf)..., pct_map(fiber_var(pf)..., ecall(b_fb, zs...))))
end

function pp(pf::ParametricFibration)::ParametricMap
    bs = fiber_var(pf)
    zs, ks = zk_vars(pf)
    return parametric_map(type_var(pf)..., pct_map(zs..., ks..., pct_sum(bs..., call(pp(fibers(pf)), zs..., splat(call(ks..., bs...))))))
end

apns(fib::ParametricFibration)::Vector{APN} = [type_var(fib)..., fiber_var(fib)..., apns(fibers(fib))...]

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
    fzs = [v_unwrap(ecall(f, zs...)) for f in b_fb]
    result = pct_map(zs..., pct_vec(fzs...))
    return result
end

function decompose(z::APN, ov::PCTVector)::PComp
    comp(z, FiniteFibration([decompose(z, t) for t in ov], MapType(v_wrap(get_type(z)), get_type(ov))))
end

"""
𝒫(z -> expr1, expr2) = (z, k1, k2) -> 𝒫(z -> expr1)(z, k1) + 𝒫(z -> expr2)(z, k2)
"""
function pp(fib::FiniteFibration)::Map
    zs, ks = zk_vars(fib)
    result = pct_map(zs..., ks..., add(map((f, k) -> ecall(pp(f), zs..., k), fibers(fib), ks)...))
    return result
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
function maptype(b::BMap)::AbstractMapType
    result = get_type(param(b))
    isa(result, VecType) && return MapType(VecType([I()]), first(content(result)))
    isa(result, ParametricMapType) && return get_param_body(result)
    return result
end

as_map(m::BMap)::APN = param(m)

function decompose(zs::PCTVector, ov::Var)::PComp
    length(zs) == 1 && return decompose(first(zs), ov)
    const_type = MapType(get_type(zs), get_type(ov))
    i = findfirst(t -> t == ov, content(zs))
    i === nothing && return comp(zs, Pconst(ov, const_type))
    return comp(zs, Pconst(constant(i), MapType(get_type(zs), N())), BMap(zs))
end

function pp(b::BMap)::AbstractMap
    m = param(b)
    process_param(p::Map) = pp(decompose(p))
    # TODO: Implement the vector case.
    process_param(p::APN) = primitive_pullback(p)
    #= process_param(p::PrimitiveCall) = pp(decompose(p)) =#
    function process_param(p::Union{Var,PrimitivePullback})
        if isa(get_type(p), MapType)
            bound_types = get_content_type(get_bound_type(get_type(m)))
            n_args = length(bound_types)
            zs, ks = zk_vars(b)
            if n_args == 1
                linear(get_type(m)) || return pullback(p)
                return pct_map(zs..., ks..., call(conjugate(m), ks...))
            end
            #= new_bound = map(var, new_symbol(m, zs..., ks..., num=n_args), bound_types) =#
            pullbacks = map(z -> call(primitive_pullback(pct_map(z, call(m, zs...))), z, ks...), zs)
            return pct_map(zs..., ks..., pct_vec(pullbacks...))
        else
            type_vars = get_params(get_type(p))
            body_type = get_param_body(get_type(p))
            bound_types = get_content_type(get_bound_type(body_type))
            n_args = length(bound_types)
            zs, ks = zk_vars(b)
            if n_args == 1
                linear(get_type(m)) || return pullback(p)
                return pct_map(zs..., ks..., call(conjugate(m), ks...))
            end
            #= new_bound = map(var, new_symbol(m, zs..., ks..., num=n_args), bound_types) =#
            pullbacks = map(z -> call(primitive_pullback(pct_map(z, call(m, zs...))), z, ks...), zs)
            return parametric_map(type_vars..., pct_map(zs..., ks..., pct_vec(pullbacks...)))
        end
    end
    return process_param(m)
end

#= decompose(map::Map)::Union{PComp, Vector{PComp}} = v_unwrap([decompose(t, get_body(map)) for t in content(ff(map))]) =#
decompose(map::Map)::Union{PComp,Vector{PComp}} = decompose(get_bound(map), get_body(map))

pretty(b::BMap) = return "ℳ $(pretty(param(b)))"

struct BPullback <: ABF
    param::PCTVector
    maptype::MapType
end

function decompose(z::APN, ov::AbstractCall)::PComp
    if isa(mapp(ov), PrimitivePullback) && !isa(get_body_type(get_type(mapp(ov))), VecType)
        zs..., k = content(args(ov))
        if any(t -> contains_name(z, get_body(t)), get_free(k)) # && isa(get_type(k), ElementType)
            @warn "potential bug. Be aware"
            maptype = MapType(VecType([get_type(k)]), get_type(ov))
            bp = BPullback(pct_vec(mapp(ov), zs...), maptype)
            return push(decompose(z, k), bp)
        end
    end
    length(args(ov)) == 1 && return push(decompose(z, first(args(ov))), BMap(mapp(ov)))
    push(decompose(z, args(ov)), BMap(mapp(ov)))
end

function as_map(bp::BPullback)
    m, args... = content(param(bp))
    zs = z_vars(bp)
    return pct_map(zs..., call(m, args..., zs...))
end

"""
z -> 𝒫 g(x, z)  is a linear map, so its pullback is the adjoint.
𝒫(z -> 𝒫 g(x, z))(z, k) = = conj(z->𝒫 g(x, z))(k)
"""
function pp(bp::BPullback)
    zs, ks = zk_vars(bp)
    return pct_map(zs..., ks..., call(conjugate(as_map(bp)), ks...))
end
pretty(bp::BPullback) = pretty(as_map(bp))


v_wrap(n::APN)::PCTVector = pct_vec(n)
v_wrap(n::T) where {T<:Union{ElementType,MapType}} = VecType([n])
v_wrap(n::T) where {T<:Union{PCTVector,VecType}} = n
v_unwrap(n::Union{PCTVector,Vector,VecType}) = length(n) == 1 ? first(n) : n
v_unwrap(n::APN) = n


struct CopyComp <: ABF
    maptype::MapType
end


function decompose(z::APN, l::Let)
    free = get_free(l)
    captures = pct_vec(filter!(t -> !(t in v_wrap(z)), free)...)
    result = decompose(z, let_copy_to_comp(captures, l))
    return result
end

function decompose(z::APN, ov::RevComposition)
    body = pct_vec(reverse(content(get_body(ov)))...)
    maptype = MapType(get_type(body), get_type(ov))
    return push(decompose(z, body), CopyComp(maptype))
end

function as_map(cc::CopyComp)
    zs = z_vars(cc)
    return pct_map(zs..., composite(zs...))
end


param(::CopyComp)::Nothing = nothing

function pretty(c::CopyComp)
    "Ω̄"
end


function copy_comp_bounds(prefix, types)
    bounds = []
    for i = 1:length(types)
        bound_name = "$(prefix)_$(i)"
        if isa(types[i], VecType)
            push!(bounds, map(var, [Symbol("$(bound_name)_$(j)") for j in 1:length(types[i])],
                get_content_type(types[i])))
        else
            push!(bounds, var(Symbol(bound_name), types[i]))
        end
    end
    return bounds
end

"""
   
x0 -> y1 -> y2 -> y3
↓  f1 ↓  f2 ↓  f3
k3 <- k2 <- k1 <- k0
"""

function pp(cc::CopyComp)
    its = get_content_type(input_type(cc))
    func_input_types = map(get_bound_type, its)
    func_output_types = map(get_body_type, its)
    ots = v_wrap(output_type(cc))
    y_0_type = first(func_input_types) |> get_content_type
    x_0 = pct_vec(map(var, new_symbol(; num=length(y_0_type), symbol=:_x), y_0_type)...)
    k_0 = pct_vec(map(var, new_symbol(; num=length(ots), symbol=:_k), ots)...)
    l_0 = pct_vec(map((k, x) -> call(k, x), content(k_0), content(x_0))...)
    if length(y_0_type) == 0
        l_0 = pct_vec(map(k -> call(k), content(k_0))...)
    end
    x_0 = v_unwrap(x_0)
    k_0 = v_unwrap(k_0)
    l_0 = v_unwrap(l_0)

    fs = map(var, new_symbol(; num=length(its), symbol=:_f), its)

    ys = map(pct_copy, map(var, new_symbol(; num=length(its), symbol=:_y), func_output_types))
    ls = map(pct_copy, map(var, new_symbol(; num=length(its), symbol=:_l), v_unwrap.(reverse(func_input_types))))
    N = length(fs)
    ys_values = Vector{APN}(undef, N)
    for i in 0:N-1
        y_prev = i == 0 ? x_0 : get_body(ys[i])
        ys_values[i+1] = call(fs[i+1], splat(y_prev))
    end

    ls_values = Vector{APN}(undef, N)
    for i in 0:N-1
        y_feed = i == N - 1 ? x_0 : get_body(ys[N-i-1])
        l_prev = i == 0 ? l_0 : get_body(ls[i])
        ls_values[i+1] = call(primitive_pullback(fs[N-i]), splat(y_feed), splat(l_prev))
    end

    function body_elem(m::Int)
        y_prev = m == 1 ? x_0 : get_body(ys[m-1])
        l_next = m == N ? l_0 : get_body(ls[N-m])
        λ = map(var, new_symbol(; num=length(v_wrap(get_type(y_prev))), symbol=:_λ), v_wrap(get_type(y_prev)))
        b = delta(y_prev, v_unwrap(pct_vec(λ...)), l_next)
        return pct_map(λ..., pct_sum(v_wrap(x_0)..., pct_let(ys..., ls[1:end-1]...,
            ys_values..., ls_values[1:end-1]..., b)))
    end
    body = map(body_elem, 1:N)

    result = pct_map(fs..., k_0, pct_vec(body...))
    return result
end

struct BLetConst <: ABF
    param::PCTVector
    maptype::MapType
end

function decompose(z::APN, ov::Let)::PComp
    params = pct_vec(get_bound(ov), args(ov))
    contains_name(params, get_body(z)) && error("The input variables currently cannot appear in a const expression.")
    maptype = MapType(v_wrap(get_type(ov)), get_type(ov))
    lc = BLetConst(params, maptype)
    return push(decompose(z, get_body(ov)), lc)
end

function as_map(lc::BLetConst)
    bounds, args = param(lc)
    zs = z_vars(lc)
    result = pct_map(zs..., pct_let(bounds..., args..., zs...))
    return result
end

"""
𝒫 (z -> let ... z end)(z, k) = let ... k end
"""
function pp(lc::BLetConst)
    zs, ks = zk_vars(lc)
    result = pct_map(zs..., ks..., call(as_map(lc), ks...))
    return result
end

#= function pp(cc::CopyComp)
    its = get_content_type(input_type(cc))
    func_input_types = map(get_bound_type, its)
    func_output_types = map(get_body_type, its)
    ots = v_wrap(output_type(cc))
    y_0_type = first(func_input_types) |> get_content_type
    #= x_0 = pct_vec(map(var, new_symbol(; num=length(y_0_type), symbol=:_x), y_0_type)...)
    k_0 = pct_vec(map(var, new_symbol(; num=length(ots), symbol=:_k), ots)...) =#

    x_0 = pct_vec(copy_comp_bounds(:_x, y_0_type)...)
    k_0 = pct_vec(copy_comp_bounds(:_k, ots)...)
    l_0 = pct_vec(map((k, x) -> call(k, x), content(k_0), content(x_0))...)
    x_0 = v_unwrap(x_0)
    k_0 = v_unwrap(k_0)
    l_0 = v_unwrap(l_0)

    fs = map(var, new_symbol(; num=length(its), symbol=:_f), its)

    #= ys = map(pct_copy, map(var, new_symbol(; num=length(its), symbol=:_y), func_output_types))
    ls = map(pct_copy, map(var, new_symbol(; num=length(its), symbol=:_l), v_unwrap.(reverse(func_input_types)))) =#

    #= ys = map(pct_copy, map(var, new_symbol(; num=length(its), symbol=:_y), func_output_types))
    ls = map(pct_copy, map(var, new_symbol(; num=length(its), symbol=:_l), v_unwrap.(reverse(func_input_types)))) =#


    ys_no_copy = copy_comp_bounds(:_y, func_output_types)
    ls_no_copy = copy_comp_bounds(:_l, v_unwrap.(reverse(func_input_types)))
    ys, ls = [], []
    for i in 1:length(ys_no_copy)
        if isa(ys_no_copy[i], Var)
            push!(ys, pct_copy(ys_no_copy[i]))
        else
            push!(ys, pct_vec(map(pct_copy, ys_no_copy[i])...))
        end
        if isa(ls_no_copy[i], Var)
            push!(ls, pct_copy(ls_no_copy[i]))
        else
            push!(ls, pct_vec(map(pct_copy, ls_no_copy[i])...))
        end
    end

    N = length(fs)
    ys_values = Vector{APN}(undef, N)
    for i in 0:N-1
        y_prev = i == 0 ? v_wrap(x_0) : get_body.(v_wrap(ys[i]))
        ys_values[i+1] = call(fs[i+1], y_prev...)
    end

    ls_values = Vector{APN}(undef, N)
    for i in 0:N-1
        y_feed = i == N - 1 ? v_wrap(x_0) : get_body.(v_wrap(ys[N-i-1]))
        l_prev = i == 0 ? v_wrap(l_0) : get_body.(v_wrap(ls[i]))
        ls_values[i+1] = call(primitive_pullback(fs[N-i]), y_feed..., l_prev...)
    end

    function body_elem(m::Int)
        y_prev = m == 1 ? v_wrap(x_0) : get_body.(v_wrap(ys[m-1]))
        l_next = m == N ? v_wrap(l_0) : get_body.(v_wrap(ls[N-m]))
        #= λ = var(:_λ, get_type(y_prev)) =#
        λ = copy_comp_bounds(:_λ, get_type.(y_prev))
        b = delta(y_prev..., λ..., v_unwrap(pct_vec(l_next...)))
        return pct_map(λ..., pct_sum(x_0, pct_let(ys..., ls[1:end-1]...,
            ys_values..., ls_values[1:end-1]..., b)))
    end
    body = map(body_elem, 1:N)

    result = pct_map(fs..., k_0, pct_vec(body...))
    return result
end =#

export Upper, Lower, all_bounds, bound

abstract type ZeroCompare end
struct IsNeg <: ZeroCompare end
struct NonNeg <: ZeroCompare end
struct IsPos <: ZeroCompare end
struct NonPos <: ZeroCompare end
struct IsZero <: ZeroCompare end
struct Uncomparable <: ZeroCompare end

abstract type Bound end
struct Upper <: Bound end
struct Lower <: Bound end

get_sign(::Upper) = constant(1)
get_sign(::Lower) = constant(-1)
(b::Upper)(d::Domain) = upper(d)
(b::Lower)(d::Domain) = lower(d)


(b::Upper)(::ElementType) = infty()
(b::Lower)(::ElementType) = minfty()
(b::Lower)(::N) = constant(1)
flip(::Upper) = Lower()
flip(::Lower) = Upper()


function bound(x::Var, y::Var, b::Bound)
    name(x) == name(y) || return y
    return b(get_type(y))
end


function bound(x::Var, m::Mul, b::Bound)
    new_content = []
    for t in content(get_body(m))
        if x in variables(t)
            x == t || error("nonlinear functions not supported")
        else
            push!(new_content, t)
            continue
        end
    end

    prefactor = mul(new_content...)

    x_bound = if isa(zero_compare(prefactor), Union{IsPos,NonNeg})
        bound(x, x, b)
    elseif isa(zero_compare(prefactor), Union{IsNeg,NonPos})
        bound(x, x, flip(b))
    else
        return b(R())
    end
    return mul(prefactor, x_bound)
end

function bound(x::Var, a::Add, b::Bound)
    return add(map(t -> bound(x, t, b), content(get_body(a)))...)
end

bound(::Var, a::Constant, ::Bound) = a


function zero_compare(c::Constant)
    get_body(c) == 0 && return IsZero()
    get_body(c) > 0 && return IsPos()
    get_body(c) < 0 && return IsNeg()
end

function zero_compare(t::APN)

    upper_bounds = [all_bounds(t, Upper(), false)...]
    lower_bounds = [all_bounds(t, Lower(), false)...]
    upper_compare = map(zero_compare, upper_bounds)
    lower_compare = map(zero_compare, lower_bounds)

    IsZero() in lower_compare && IsZero in upper_compare && return IsZero()

    IsNeg() in upper_compare && return IsNeg()
    IsZero() in upper_compare && return NonPos()
    NonPos() in upper_compare && return NonPos()

    IsPos() in lower_compare && return IsPos()
    IsZero() in lower_compare && return NonNeg()
    NonNeg() in lower_compare && return NonNeg()

    return Uncomparable()
end

function all_bounds(t::APN, b::Bound, include_self=true)
    bounds = Set{APN}()
    include_self && push!(bounds, t)

    for v in variables(t)
        v == infty() && continue
        subtree = all_bounds(bound(v, t, b), b)
        union!(bounds, subtree)
    end
    return bounds
end



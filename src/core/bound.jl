export Upper, Lower, all_bounds, bound

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
    isa(get_type(y), Domain) || return mul(get_sign(b), infty()) 
    return b(get_type(y))
end


function bound(x::Var, m::Mul, b::Bound)
    new_content = []
    for t in content(m)
        x in variables(t) || (push!(new_content, t) && continue)
        x == t || error("nonlinear functions not supported")
    end

    prefactor = mul(new_content...)
    x_bound = get_sign(prefactor) == 1 ? bound(x, x, b) : bound(x, x, flip(b))
    return mul(prefactor, x_bound)
end

function bound(x::Var, a::Add, b::Bound)
    return add(map(t->bound(x, t, b), content(a))...)
end


function get_sign(c::Constant)
    return sign(get_body(c))
end

function get_sign(t::APN)
    upper_bounds = all_bounds(t, Upper())
    lower_bounds = all_bounds(t, Lower())
    any(b->isa(b, Constant) && get_body(b) < 0, upper_bounds) && return -1
    any(b->isa(b, Constant) && get_body(b) > 0, lower_bounds) && return 1
    constant(0) in upper_bounds && constant(0) in lower_bounds && return 0
    return NaN
end

function all_bounds(t::APN, b::Bound)
    bounds = Set{APN}([first(simplify(t))])
    for v in variables(t)
        v == infty() && continue
        subtree = all_bounds(bound(v, t, b), b)
        union!(bounds, subtree)
    end
    return bounds
end



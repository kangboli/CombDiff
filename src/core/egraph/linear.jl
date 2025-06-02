is_linear(n::APN) = false



function is_linear(m::Map)
    return is_pullback_kf(m)
end

function is_linear(fd::Fold)
    return is_linear(get_body(fd))
end

is_pullback_kf(m::APN) = false

function is_pullback_kf(m::Map)
    bounds, body = get_bound(m), get_body(m)

    isa(body, PrimitiveCall) || return false
    p = mapp(body)
    isa(p, AbstractPullback) || return false
    x_type = get_body_type(get_type(p))
    ks = args(body)[length(v_wrap(x_type))+1:end]

    f = get_body(p)

    f == bounds && return true
    ks == bounds && return true
    return false
end



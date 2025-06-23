export let_to_call, is_split, split_let, call_to_let
abstract type AbstractWithMemory end

is_split(n::APN) = true

is_split(n::AbstractWithMemory) = is_split(get_body(n))

function is_split(l::Let)
    return length(get_bound(l)) == 1 && is_split(get_body(l))
end

split_let(n::APN) = n

split_let(n::AbstractWithMemory) = with_memory(get_memory(n), split_let(n))

function split_let(l::Let)
    foldr(((b, a), body) -> pct_let(b, a, body), zip(get_bound(l), args(l)); init=split_let(get_body(l)))
end

is_combined(m::AbstractWithMemory) = is_combined(get_body(m))

is_combined(l::Let) = !isa(get_body(l), Let) 

combine_let(n::AbstractWithMemory) = with_memory(get_memory(n), combine_let(get_body(n)))

function combine_let(l::Let)
    is_combined(l) && return l
    new_body = combine_let(get_body(l))
    return pct_let(get_bound(l)..., get_bound(new_body)..., args(l)..., args(new_body)..., get_body(new_body))
end

let_to_call(n::APN) = n

function let_to_call(l::Let)
    is_split(l) || return let_to_call(split_let(l))
    call(pct_map(get_bound(l)..., let_to_call(get_body(l))), args(l)...)
end

call_to_let(n::APN) = n

call_to_let(n::AbstractWithMemory) = with_memory(get_memory(n), call_to_let(get_body(n)))

function call_to_let(c::PrimitiveCall)
    m = mapp(c)
    return combine_let(pct_let(get_bound(m)..., args(c)..., call_to_let(get_body(m))))
end

export @cascade, combine_add

macro cascade(f)
    esc(:(begin
        PCT.$(f)(n::APN) = set_terms!(n, map(PCT.$(f), terms(n))...)
        PCT.$(f)(t::TerminalNode) = t
    end))
end

function combine_add(s::Add)
    d = Dict()
    one = make_node!(Constant, 1)
    process_term!(t::APN) = d[t] = get!(d, t, 0) + 1
    process_term!(c::Constant) = d[one] = get!(d, c, 0) + content(c)
    process_term!(m::Mul) = let (c, n) = split_constant(m)
        d[n] = get!(d, n, 0) + content(c)
    end
    map(process_term!, content(s))
    filter!(((k, v),)->abs(v) > 1e-7, d)

    mul_term(k, v) = v == 1 ? k : make_node!(Mul, make_node!(PCTVector, make_node!(Constant, v), k))
    make_node!(Add, make_node!(PCTVector, [combine_add(mul_term(k, v)) for (k, v) in d]...))
end

@cascade combine_add



using CombDiff

f, ctx = @pct begin
    @space V begin
        type = (I,) -> C
    end

    @space H begin
        type = (I, I) -> C
        symmetries = (((2, 1), :conj),)
    end
    (A::H) -> _
end

g = get_body(@pct f ctx (x::V) -> sum((i, j), x(i)' * A(i, j) * x(j)))
cg = decompose(g)
pcg = pp(cg)
pcg_1 = propagate_k(pcg)

pcg_2 = simplify(pcg_1) |> first
simplify(pcg_2; settings=symmetry_settings) |> first


f, ctx = @pct begin
    @space H begin
        type = (I, I) -> C
        symmetries = (((2, 1), :conj),)
    end

    @space V begin
        type = (I,) -> C
    end

    @space T begin
        type = (I, I, I, I) -> C
        symmetries = (((2, 1, 4, 3), :conj), ((3, 4, 1, 2), :id))
    end

    @space U begin
        type = (I, I) -> C
    end

    (A::H, J::T) -> _
end

g = get_body(@pct f ctx (C::U) -> sum((i, j, p, q, r, s),
    C(p, i)' * C(q, i) * C(r, j)' * C(s, j) * J(p, q, r, s)))

cg = decompose(g)
pcg = pp(cg)
pcg_1 = propagate_k(pcg)

pcg_2 = simplify(pcg_1) |> first
pcg_3 = simplify(pcg_2; settings=symmetry_settings) |> first


f, ctx = @pct begin

    @domain P begin
        base = I
        lower = -N
        upper = N - 1
        periodic = true
    end

    @domain Q begin
        base = I
        lower = -N
        upper = N
        contractable = false
    end

    @space Mmn begin
        type = (I, I, I, I) -> C
        symmetries = (((2, 1, 4, 3), :conj),)
    end

    @space Sym begin
        type = (I,) -> C
        symmetries = (((1,), :ineg),)
    end

    @space Gauge begin
        type = (I, I, I) -> C
    end

    @space Density begin
        type = (I, I) -> C
    end

    (S::Mmn, w::Sym) -> _
end

g = get_body(@pct f ctx (U::Gauge) -> ((ρ::Density) -> sum((n::I, b::Q), ρ(n, b)' * ρ(n, b)))(
    (n::I, b::Q) -> sum((k::P, p, q), U(p, n, k)' * S(p, q, k, k + b) * U(q, n, k + b))))

cg = decompose(eval_all(g))
pcg = pp(cg)
pcg_1 = eval_all(propagate_k(pcg))
pcg_2 = simplify(pcg_1) |> first
pcg_3 = simplify(pcg_2; settings=symmetry_settings) |> first

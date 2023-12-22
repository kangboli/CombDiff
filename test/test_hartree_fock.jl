using PCT, Test

@testset "Hartree Fock" begin

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

    g = fc(@pct f ctx (C::U) -> sum((i, j, p, q, r, s), C(p, i)' * C(q, i) * C(r, j)' * C(s, j) * J(p, q, r, s)))
    cg = decompose(g)

    pcg = pp(cg)
    pcg_1 = propagate_k(pcg)
    pcg_2 = simplify(pcg_1) |> first
    pcg_3 = simplify(pcg_2; settings=symmetry_settings) |> first

end

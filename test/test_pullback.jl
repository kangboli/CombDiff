@testset "univariate" begin
    f, ctx = @pct (x::R, y::R, _K::C) -> _

    # Identity map
    p = @pct f ctx pullback((m::R) -> m)
    p1 = reduce_pullback(fc(p)) |> first
    @test fc(eval_all(p1)) == var(:_K, R())

    # Trivial map
    p = @pct f ctx pullback((m::R) -> x)
    p1 = reduce_pullback(fc(p)) |> first
    @test fc(eval_all(p1)) == constant(0)

    # Complex identity
    p = @pct f ctx pullback((m::C) -> m)
    p1 = reduce_pullback(fc(p)) |> first
    @test fc(eval_all(p1)) == var(:_K, C())

    # Complex conjugate
    p = @pct f ctx pullback((m::C) -> m')
    p1 = reduce_pullback(fc(p)) |> first
    @test fc(eval_all(p1)) == conjugate(var(:_K, C()))

    # Monomials
    p = @pct f ctx pullback((m::C) -> m^2)
    p1 = reduce_pullback(fc(p)) |> first
    @test fc(eval_all(p1)) == fc(fc(@pct f ctx (m::C) -> (2 * (m^((2 + (-1))))' * _K)))

end

@testset "call" begin
    #= f, ctx = @pct (x::C) -> _ =#
    f, ctx = @pct pullback((x::C) -> ((y::C) -> y)(x))
    p1 = eval_all(first(reduce_pullback(eval_all(f))))
    p2 = eval_all(first(reduce_pullback(f)))
    p1 == p2
end

@testset "contraction" begin
    f, ctx = @pct begin
        @space H begin
            type = (I, I) -> C
            symmetries = (((2, 1), :conj),)
        end
        @space V begin
            type = (I,) -> C
        end

        (A::H) -> _
    end

    f1 = @pct f ctx pullback((x::V) -> sum((i, j), x(i)' * A(i, j) * x(j)))
    #= f1 = @pct f ctx (x::V) -> sum((i, j), x(i)' * A(i, j) * x(j)) =#
    f2 = fc(eval_all(reduce_pullback(f1)))
    f3 = eval_all(call(f2, first(ff(f2)), constant(1)))
    

    result = simplify(f3) |> first
    Profile.clear()
    @time @profile simplify(f2) |> first
    pprof()
    #= @pct f ctx x(::V) -> sum((i, j), x(i)' * A(i, j) * x(j)) =#
    x = var(:x, I())
    s, _ = @pct sum(i, i)
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

    g = @pct f ctx pullback((C::U) -> sum((i,j,p,q,r,s), C(p,i)' * C(q,i) * C(r,j)' * C(s,j) * J(p,q,r,s)))

    p = fc(eval_all(reduce_pullback(g)))

    q = eval_all(call(p, first(ff(p)), constant(1)))

    result = simplify(q) |> first
    s_1, s_2 = content(fc(fc(fc(result))[2]))

    s_1_sigs = [SignatureTree(ff(s_1)[i], fc(s_1), content(ff(s_1))[1:end .!= i]) for i in 1:length(ff(s_1))]
    s_2_sigs = [SignatureTree(ff(s_2)[i], fc(s_2), content(ff(s_2))[1:end .!= i]) for i in 1:length(ff(s_2))]
    s_1_sigs[2] == s_2_sigs[3]
    s_1_sigs[2] 
    s_2_sigs[3]
end

@testset "Wannier" begin
    f, ctx = @pct begin 

        @domain P begin
            base = I
            lower = -N
            upper = N-1
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
            symmetries = (((2, 1, 4, 3), :conj), )
        end

        @space Sym begin
            type = (I, ) -> C
            symmetries = (((1, ), :ineg), )
        end

        @space Gauge begin
            type = (I, I, I) -> C
        end

        @space Density begin
            type = (I, I) -> C
        end

        #= @space SymC begin
            type = (I, ) -> C
            symmetries = (((1, ), :inegc), )
        end =#

        (S::Mmn, w::Sym) -> _
    end

    g = @pct f ctx pullback((U::Gauge) -> ((ρ::Density) -> sum((n::I, b::Q), ρ(n, b)' * ρ(n, b)))(
        (n::I, b::Q) -> sum((k::P, p, q), U(p, n, k)' * S(p,q,k,k+b) * U(q, n, k+b))))
    eval_all(g)
    g_1 = fc(eval_all(reduce_pullback(eval_all(g))))
    g_2 = eval_all(call(g_1, first(ff(g_1)), constant(1)))
    @profview neighbors(fc(fc(g_2)))

    @time g_3 = simplify(g_2) |> first
    a, b = content(fc(first(fc(fc(g_3)))))
    b_s = simplify(b, settings=Dict(:symmetry=>true))
    g_4 = simplify(g_3, settings=Dict(:symmetry=>true))

    fc(fc(g)) |> neighbors
    fc(fc(g)) |> neighbors |> first |> first |> neighbors 
    println(verbose(fc(fc(g))))

end



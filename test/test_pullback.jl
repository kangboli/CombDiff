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
    @test fc(eval_all(p1)) == fc(fc(@pct f ctx (m::C)->(2 * (m^((2+(-1))))' * _K)))

end

@testset "call" begin
    #= f, ctx = @pct (x::C) -> _ =#
    f, ctx = @pct pullback((x::C)->((y::C) -> y)(x))
    p1 = eval_all(first(reduce_pullback(eval_all(f))))
    p2 = eval_all(first(reduce_pullback(f)))
    p1 == p2
end

@testset "contraction" begin
    f, ctx = @pct begin
        @space H begin
            type=(I, I) -> C
            symmetries=(((2,1), :conj),)
        end
        @space V begin
            type=(I, ) -> C
        end

        (A::H) -> _
    end

    f1 = @pct f ctx pullback((x::V) -> sum((i, j), x(i)' * A(i, j) * x(j)))
    f2 = eval_all(reduce_pullback(f1))

    Profile.clear()
    @time @profile simplify(f2) |> first
    pprof()
    #= @pct f ctx x(::V) -> sum((i, j), x(i)' * A(i, j) * x(j)) =#
    x = var(:x, I())
    s, _ = @pct sum(i, i)
end



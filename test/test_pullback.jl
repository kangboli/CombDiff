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
    f1 = @pct f ctx (x::V) -> sum((i, j), x(i)' * A(i, j) * x(j))
    f1 = @pct f ctx (x::V) -> sum((i, j), x(i)' * A(i, j) * x(j))
    f2 = eval_all(reduce_pullback(f1))

    simplify(f2) |> first
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

    s  = simplify(q) |> first

    simplify(@pct f ctx (x::I) -> x + x) |> first
    simplify(@pct f ctx (i::I, j::I) -> A(i, j) + A(j, i)') |> first
    q
end

@testset "pbev"  begin

    f, ctx = @pct (x::R, y::R, _K::C) -> _

    # Identity map
    p = @pct f ctx pullback((m::R) -> m)
    p1 = reduce_pullback(fc(p)) 
    @test fc(eval_all(p1)) == var(:_K, R())
    
    # Trivial map
    p = @pct f ctx pullback((m::R) -> x)
    p1 = reduce_pullback(fc(p)) 
    @test fc(eval_all(p1)) == constant(0)

    # Complex identity
    p = @pct f ctx pullback((m::C) -> m)
    p1 = reduce_pullback(fc(p)) 
    @test fc(eval_all(p1)) == var(:_K, C())

    # Complex conjugate
    p = @pct f ctx pullback((m::C) -> m')
    p1 = reduce_pullback(fc(p)) 
    @test fc(eval_all(p1)) == conjugate(var(:_K, C()))

    # Monomials (not yet implemented) 
    #= p = @pct f ctx pullback((m::C) -> m^2)
    p1 = reduce_pullback(fc(p)) 
    @test fc(eval_all(p1)) == fc(fc(@pct f ctx (m::C) -> (2 * (m^((2 + (-1))))' * _K))) =#
end
    

@testset "pbev contraction" begin

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
    f2 = eval_all(reduce_pullback(f1))
    simplify(fc(f2)) |> first

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

    @pct f ctx sum((p,q,r,s), J(p,q,r,s)) 
    @pct f ctx sum((p,q,r,s), J(r,s,p,q)) 
    @pct f ctx sum((p,q,r,s), J(s,r,q,p)') 

    p = fc(eval_all(reduce_pullback(g)))

    q = eval_all(call(p, first(ff(p)), constant(1)))

    s  = simplify(q) |> first

end

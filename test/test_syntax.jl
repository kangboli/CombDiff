using PCT, Test

@testset "domain" begin
    d, ctx = @pct begin
        @domain I1 begin
            base = I
            lower = -N
            upper = N
        end
    end

    @test base(d) == I()
    @test lower(d) == mul(constant(-1), var(:N, I()))
    @test upper(d) == var(:N, I())
    @test d == ctx[:I1]

    d2 = @pct _ ctx begin
        @domain I2 begin
            base = R
            lower = -X
            upper = X
        end
    end

    @test base(d2) == R()
    @test lower(d2) == mul(constant(-1), var(:X, R()))
    @test upper(d2) == var(:X, R())
    @test d2 == ctx[:I2]

    d3 = @pct _ ctx (x::I1) -> x
    @test fc(d3) == var(:x, ctx[:I1])
end

@testset "space" begin
    s, ctx = @pct begin
        @space V begin
            type = (I,) -> R
        end
    end

    @test from(s) == VecType([I()])
    @test content(s) == R()
    @test ctx[:V] == s

    s2 = @pct _ ctx begin
        @space M begin
            type = (I, I) -> R
        end
    end

    @test from(s2) == VecType([I(), I()])
    @test content(s2) == R()
    @test ctx[:M] == s2

    f = @pct _ ctx (x::M) -> x
    @test fc(f) == var(:x, ctx[:M])

    s3 = @pct _ ctx begin
        @space S begin
            type = (I, I) -> R
            symmetries = (((2, 1), :id),)
        end
    end

    @test first(symmetries(s3)) == ((2, 1), :id)
end


@testset "Map" begin
    f, _ = @pct (x::I) -> x
    @test fc(f) == var(:x, I())
    @test ff(f) == pct_vec(var(:x, I()))

    f, ctx = @pct begin
        @space M begin
            type = (I, I) -> R
        end

        (x::M) -> (i::I, j::I) -> x(i, j)
    end

    @test fc(fc(f)) == call(var(:x, MapType(VecType([I(), I()]), R())), var(:i, I()), var(:j, I()))
    @test ff(f) == pct_vec(var(:x, ctx[:M]))

    g = @pct _ ctx begin
        (x::M) -> (x(i)) -> x(i)
    end
    @test fc(ff(fc(g))) == call(var(:x, ctx[:M]), var(:i, I()))

    h = @pct _ ctx begin
        (j::I) -> ((i::I) -> 2 * i)(j)
    end
    @test ff(h) == pct_vec(var(:j, I()))
end

@testset "arithmatic" begin
    _, ctx = @pct begin
        @space M begin
            type = (I, I) -> R
        end
    end

    f, _ = @pct (i::I) -> i + i + 2
    @test fc(f) == add(var(:i, I()), var(:i, I()), constant(2))

    f, _ = @pct (i::I, j::I) -> i * j * 2
    @test fc(f) == mul(var(:i, I()), var(:j, I()), constant(2))

    f, _ = @pct (i::I) -> -i + 2
    @test fc(f) == add(mul(constant(-1), var(:i, I())), constant(2))

    f, _ = @pct (i::I) -> i^(-1)
    @test fc(f) == monomial(var(:i, I()), constant(-1))

    f, _ = @pct (i::I, j::I) -> (i * j) * (2 + 1)
    @test fc(f) == mul(var(:i, I()), var(:j, I()), add(constant(2), constant(1)))

    f = @pct _ ctx begin
        (x::M, i::I, j::I) -> x(i, j) * x(j, i) + j
    end
    @test fc(f) == add(mul(call(var(:x, ctx[:M]), var(:i, I()), var(:j, I())),
            call(var(:x, ctx[:M]), var(:j, I()), var(:i, I()))), var(:j, I()))

end

@testset "Contraction and Product" begin
    f, _ = @pct sum(i, 2*i)
    @test f == pct_sum(var(:i, I()), mul(constant(2), var(:i, I())))

    # Multiple indices gives multiple sums
    f, _ = @pct sum((i, j, k), i * j * k)
    @test fc(fc(fc(f))) == mul(var(:i, I()), var(:j, I()), var(:k, I()))

    f, _ = @pct prod(i, i^2)
    @test f == pct_product(var(:i, I()), monomial(var(:i, I()), constant(2)))

    _, ctx = @pct begin
        @domain I1 begin
            base=I
            lower=-N
            upper=N
        end
        @domain I2 begin
            base=I
            lower=-M
            upper=M
        end
        @domain R1 begin
            base=R
            lower=-E
            upper=E
        end
    end

    g = @pct _ ctx begin
        sum(i::I1, i*2)
    end
    @test ff(g) == var(:i, ctx[:I1])

    g = @pct _ ctx begin
        sum((i::I1, j::I2), i * j)
    end

    @test ff(g) == var(:i, ctx[:I1])
    @test ff(fc(g)) == var(:j, ctx[:I2])

    g = @pct _ ctx begin
        prod(i::I1, int(j::R1, i * j))
    end

end

@testset "pullback" begin
    # Pullback
    f, _ = @pct pullback((i::I) -> i * 2)
    @test fc(f) == pct_map(var(:i, I()), mul(var(:i, I()), constant(2)))

    # Short syntax for domain.
    d, ctx = @pct begin
        @domain I1 I -N N 
    end
    @test name(d) == :I1

    # Pullback of a primitive call.
    s, ctx = @pct begin
        @space V begin
            type=(I,)->R
        end
    end
    f = @pct _ ctx (x::V, j::I) -> pullback((x(i)) -> x(j))
    @test isa(fc(f), Pullback)

    # A primitive pullback.
    f = @pct _ ctx (x::V) -> pullback(x)
    @test isa(fc(f), PrimitivePullback)
end

@testset "Other" begin
    f, ctx = @pct begin
        @space S begin
            type=(I, I) -> R
        end
        (A::S) -> _
    end
    g = @pct f ctx (i::I, j::I) -> delta(i, j, A(i, j))
    @test fc(fc(g)) == delta(var(:i, I()), var(:j, I()), call(var(:A, ctx[:S]), var(:i, I()), var(:j, I())))

    f, _ = @pct (i::C) -> i'
    @test fc(f) == conjugate(var(:i, C()))
end


using CombDiff, Test

@testset "syntax: domain" begin
    d, ctx = @pct begin
        @domain I1 begin
            base = I
            lower = -N
            upper = N
        end
    end

    @test d == var(:_)
    @test base(ctx[:I1]) == I()
    @test lower(ctx[:I1]) == mul(constant(-1), var(:N, UndeterminedPCTType()))
    @test upper(ctx[:I1]) == var(:N, UndeterminedPCTType())

    d2, ctx = @pct _ ctx begin
        @domain I2 R{-N,N}
    end

    @test d2 == var(:_)
    @test lower(ctx[:I2]) == mul(constant(-1), var(:N, UndeterminedPCTType()))
    @test upper(ctx[:I2]) == var(:N, UndeterminedPCTType())
    # @test d2 == ctx[:I2]

    let N = 2.0
        d3, _ = @main :((x::I1) -> x) _ ctx
        @test get_body(get_body(d3)) == var(:x, ctx[:I1])
    end
end

@testset "syntax: space" begin
    _, ctx = @pct begin
        @space V begin
            type = (I,) -> R
        end
    end
    s = ctx[:V]

    @test get_bound_type(s) == VecType([I()])
    @test get_body_type(s) == R()

    _, ctx = @pct _ ctx begin
        @space M begin
            type = (I, I) -> R
        end
    end
    s2 = ctx[:M]

    @test get_bound_type(s2) == VecType([I(), I()])
    @test get_body_type(s2) == R()
    # @test ctx[:M] == s2

    f, _ = @main (x::M) -> x _ ctx
    @test get_body(get_body(f)) == var(:x, ctx[:M])

    _, ctx = @pct _ ctx begin
        @space S begin
            type = (I, I) -> R
            symmetries = (f -> (i, j) -> f(j, i),)
        end
    end
    s3 = ctx[:S]

    @test first(symmetries(s3)) == pct_map(var(:f), pct_map(var(:i), var(:j), call(var(:f), var(:j), var(:i))))
end


@testset "syntax: map" begin
    f, _ = @main (x::I) -> x
    f = get_body(f)
    @test get_body(f) == var(:x, I())
    @test get_bound(f) == pct_vec(var(:x, I()))

    _, ctx = @pct begin
        @space M begin
            type = (I, I) -> R
        end
    end

    f, _ = @main (x::M) -> (i::I, j::I) -> x(i, j) _ ctx
    f = get_body(f)

    @test get_body(get_body(f)) == call(var(:x, MapType(VecType([I(), I()]), R())), var(:i, I()), var(:j, I()))
    @test get_bound(f) == pct_vec(var(:x, ctx[:M]))

    g, _ = @main (x::M) -> (i::I) -> x(i) _ ctx
    g = get_body(g)
    @test first(content(get_bound(get_body(g)))) == var(:i, I())

    h, _ = @main (j::I) -> ((i::I) -> 2 * i)(j) _ ctx
    h = get_body(h)
    @test get_bound(h) == pct_vec(var(:j, I()))
end

@testset "syntax: arithmatic" begin
    _, ctx = @pct begin
        @space M begin
            type = (I, I) -> R
        end
    end

    f = get_body(first(@main (i::I) -> i + i + 2))
    @test get_body(f) == add(var(:i, I()), var(:i, I()), constant(2))

    f = get_body(first(@main (i::I, j::I) -> i * j * 2))
    @test get_body(f) == mul(var(:i, I()), var(:j, I()), constant(2))

    f = get_body(first(@main (i::I) -> -i + 2))
    @test get_body(f) == add(mul(constant(-1), var(:i, I())), constant(2))

    f = get_body(first(@main (i::I) -> i^(-1)))
    @test get_body(f) == monomial(var(:i, I()), constant(-1))

    f = get_body(first(@main (i::I, j::I) -> (i * j) * (2 + 1)))
    @test get_body(f) == mul(var(:i, I()), var(:j, I()), add(constant(2), constant(1)))

    f = get_body(first(@main (x::M, i::I, j::I) -> x(i, j) * x(j, i) + j _ ctx))
    @test get_body(f) == add(mul(call(var(:x, ctx[:M]), var(:i, I()), var(:j, I())),
            call(var(:x, ctx[:M]), var(:j, I()), var(:i, I()))), var(:j, I()))
end

@testset "syntax: contractions" begin
    f = get_body(first(@main sum(i, 2 * i)))
    @test f == pct_sum(var(:i, N()), mul(constant(2), var(:i, N())))

    # Multiple indices gives multiple sums
    f = get_body(first(@main sum((i, j, k), i * j * k)))
    @test get_body(f) == mul(var(:i, N()), var(:j, N()), var(:k, N()))

    #= f, _ = @pct prod(i, i^2)
    @test f == pct_product(var(:i, I()), monomial(var(:i, I()), constant(2))) =#

    _, ctx = @comb begin
        @domain I1 begin
            base = I
            lower = -N
            upper = N
        end
        @domain I2 begin
            base = I
            lower = -M
            upper = M
        end
        @domain R1 begin
            base = R
            lower = -E
            upper = E
        end
    end

    let (N, M, E) = (2, 3, 4.0)
        g = get_body(first(@main sum(i::I1, i) _ ctx))
        @test get_bound(g) == pct_vec(var(:i, ctx[:I1]))
    end

    let (N, M, E) = (2, 3, 4.0)
        g = get_body(first(@main sum((i::I1, j::I2), i * j) _ ctx))
        @test get_bound(g) == pct_vec(var(:i, ctx[:I1]), var(:j, ctx[:I2]))
        @test get_body(g) == mul(var(:i, ctx[:I1]), var(:j, ctx[:I2]))
    end
end

@testset "syntax: pullback" begin
    # Pullback
    f = get_body(first(@main pullback((i::I) -> i * 2)))
    @test get_body(f) == pct_map(var(:i, I()), mul(var(:i, I()), constant(2)))

    # Short syntax for domain.
    _, ctx = @comb begin
        @domain I1 I{-N,N}
    end
    d = ctx[:I1]
    @test base(d) == I()
    @test upper(d) == var(:N, UndeterminedPCTType())

    f = get_body(first(@main (i::I) -> (j::I{1,i}) -> i + j))
    @test first(get_type(get_bound(get_body(f)))) == Domain(I(), constant(1), var(:i, I()), Dict())
    # Pullback of a primitive call.
    _, ctx = @comb begin
        @space V begin
            type = (I,) -> R
        end
    end
    s = ctx[:V]
    f = get_body(first(@main (j::I) -> pullback((x::V) -> x(j)) _ ctx))
    @test isa(get_body(f), Pullback)

    # A primitive pullback.
    f = get_body(first(@main (x::V) -> pullback(x) _ ctx))
    @test isa(get_body(f), PrimitivePullback)
end


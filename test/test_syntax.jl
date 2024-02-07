using PCT, Test

@testset "syntax: domain" begin
    d, ctx = @pct begin
        @domain I1 begin
            base = I
            lower = -N
            upper = N
        end
    end

    @test d === nothing
    @test base(ctx[:I1]) == I()
    @test lower(ctx[:I1]) == mul(constant(-1), var(:N, I()))
    @test upper(ctx[:I1]) == var(:N, I())

    d2, ctx = @pct _ ctx begin
        @domain I2 begin
            base = R
            lower = -N
            upper = N
        end
    end

    @test d2 === nothing
    @test lower(ctx[:I2]) == mul(constant(-1), var(:N, R()))
    @test upper(ctx[:I2]) == var(:N, R())
    # @test d2 == ctx[:I2]

    d3, _ = @pct _ ctx (x::I1) -> x
    @test get_body(d3) == var(:x, ctx[:I1])
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

    f, _ = @pct _ ctx (x::M) -> x
    @test get_body(f) == var(:x, ctx[:M])

    _, ctx = @pct _ ctx begin
        @space S begin
            type = (I, I) -> R
            symmetries = (((2, 1), :id),)
        end
    end
    s3 = ctx[:S]

    @test first(symmetries(s3)) == ((2, 1), :id)
end


@testset "syntax: map" begin
    f, _ = @pct (x::I) -> x
    @test get_body(f) == var(:x, I())
    @test get_bound(f) == pct_vec(var(:x, I()))

    f, ctx = @pct begin
        @space M begin
            type = (I, I) -> R
        end

        (x::M) -> (i::I, j::I) -> x(i, j)
    end

    @test get_body(get_body(f)) == call(var(:x, MapType(VecType([I(), I()]), R())), var(:i, I()), var(:j, I()))
    @test get_bound(f) == pct_vec(var(:x, ctx[:M]))

    g, _ = @pct _ ctx begin
        (x::M) -> (i::I) -> x(i)
    end
    @test first(content(get_bound(get_body(g)))) == var(:i, I())

    h, _ = @pct _ ctx begin
        (j::I) -> ((i::I) -> 2 * i)(j)
    end
    @test get_bound(h) == pct_vec(var(:j, I()))
end

@testset "syntax: arithmatic" begin
    _, ctx = @pct begin
        @space M begin
            type = (I, I) -> R
        end
    end

    f, _ = @pct (i::I) -> i + i + 2
    @test get_body(f) == add(var(:i, I()), var(:i, I()), constant(2))

    f, _ = @pct (i::I, j::I) -> i * j * 2
    @test get_body(f) == mul(var(:i, I()), var(:j, I()), constant(2))

    f, _ = @pct (i::I) -> -i + 2
    @test get_body(f) == add(mul(constant(-1), var(:i, I())), constant(2))

    f, _ = @pct (i::I) -> i^(-1)
    @test get_body(f) == monomial(var(:i, I()), constant(-1))

    f, _ = @pct (i::I, j::I) -> (i * j) * (2 + 1)
    @test get_body(f) == mul(var(:i, I()), var(:j, I()), add(constant(2), constant(1)))

    f, _ = @pct _ ctx begin
        (x::M, i::I, j::I) -> x(i, j) * x(j, i) + j
    end
    @test get_body(f) == add(mul(call(var(:x, ctx[:M]), var(:i, I()), var(:j, I())),
            call(var(:x, ctx[:M]), var(:j, I()), var(:i, I()))), var(:j, I()))

end

@testset "syntax: contractions" begin
    f, _ = @pct sum(i, 2*i)
    @test f == pct_sum(var(:i, N()), mul(constant(2), var(:i, N())))

    # Multiple indices gives multiple sums
    f, _ = @pct sum((i, j, k), i * j * k)
    @test get_body(f) == mul(var(:i, N()), var(:j, N()), var(:k, N()))

    #= f, _ = @pct prod(i, i^2)
    @test f == pct_product(var(:i, I()), monomial(var(:i, I()), constant(2))) =#

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

    g, _ = @pct _ ctx begin
        sum(i::I1, i*2)
    end
    @test get_bound(g) == pct_vec(var(:i, ctx[:I1]))

    g, _ = @pct _ ctx begin
        sum((i::I1, j::I2), i * j)
    end

    @test get_bound(g) == pct_vec(var(:i, ctx[:I1]), var(:j, ctx[:I2]))
    @test get_body(g) == mul(var(:i, ctx[:I1]), var(:j, ctx[:I2]))

    #= g = @pct _ ctx begin
        prod(i::I1, int(j::R1, i * j))
    end =#
end

@testset "syntax: pullback" begin
    # Pullback
    f, _ = @pct pullback((i::I) -> i * 2)
    @test get_body(f) == pct_map(var(:i, I()), mul(var(:i, I()), constant(2)))

    # Short syntax for domain.
    _, ctx = @pct begin
        @domain I1 I -N N 
    end
    d = ctx[:I1]
    @test name(d) == :I1

    f, _ = @pct (i::I) -> (j::I ∈ (1, i)) -> i + j
    # Pullback of a primitive call.
    _, ctx = @pct begin
        @space V begin
            type=(I,)->R
        end
    end
    s = ctx[:V]
    f, _ = @pct _ ctx (j::I) -> pullback((x::V) -> x(j))
    @test isa(get_body(f), Pullback)

    # A primitive pullback.
    f, _ = @pct _ ctx (x::V) -> pullback(x)
    @test isa(get_body(f), PrimitivePullback)
end

# @testset "syntax: other" begin
#     f, ctx = @pct begin
#         @space S begin
#             type=(I, I) -> R
#         end
#         (A::S) -> _
#     end
#     g, _ = @pct f ctx (i::I, j::I) -> delta(i, j, A(i, j))
#     @test get_body(get_body(g)) == delta(var(:i, I()), var(:j, I()), call(var(:A, ctx[:S]), var(:i, I()), var(:j, I())))

#     f, _ = @pct (i::C) -> i'
#     @test get_body(f) == conjugate(var(:i, C()))
# end


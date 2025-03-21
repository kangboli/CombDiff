using CombDiff, Test

@testset "subst: free and dummy variables" begin
    f, ctx = @comb begin
        @space S begin
            type = (N, N) -> R
        end
        (A::S, i::N, j::N) -> _
    end

    f1 = get_body(first(@main A(i, j) f ctx))
    vars = variables(f1)
    @test all(t -> t in vars, [var(:A, ctx[:S]), var(:i, N()), var(:j, N())])

    f1 = get_body(first(@main sum(a, A(a, j)) f ctx))
    vars = variables(f1)
    @test var(:a, N()) in vars

    # Dummy variables
    #= _, dummies = free_and_dummy(f1)
    @test all(t -> t in dummies, [var(:A, ctx[:S]), var(:i, I()), var(:j, I()), var(:a, N())]) =#
    # Contains name
    @test all(t -> contains_name(f1, t), [:i, :j, :A, :a])
end

@testset "substitution" begin
    f, ctx = @comb begin
        @space S begin
            type = (N, N) -> N
        end
        (A::S, i::N, j::N, k::N, l::N) -> _
    end

    # simple substitution
    f1 = get_body(first(@main A(i, j) f ctx))
    f2 = get_body(first(@main A(A(i, j), j) f ctx))
    @test get_body(f2) == subst(get_body(f1), var(:i, N()), get_body(f1))

    # try to substituting a dummy variable
    f1 = get_body(first(@main sum(a, A(a, j)) f ctx))
    @test get_body(f1) == subst(get_body(f1), var(:a, I()), var(:i, I()))

    f1 = get_body(first(@main i * sum(i, A(i, j)) f ctx))
    f2 = get_body(first(@main k * sum(i, A(i, j)) f ctx))
    @test get_body(f2) == subst(get_body(f1), var(:i, N()), var(:k, N()))

    f1 = get_body(first(@main (a::I) -> A(a, j) f ctx))
    @test get_body(f1) == subst(get_body(f1), var(:a, N()), var(:i, N()))

    # Resolving conflict

    f1 = get_body(first(@main k * sum(i, A(i, j)) f ctx))
    f2 = get_body(first(@main k * sum(a, A(a, i)) f ctx))
    @test get_body(f2) == subst(get_body(f1), var(:j, N()), var(:i, N()))

    f1 = get_body(first(@main i * sum(i, sum(j, A(i, j) * k)) f ctx))
    f2 = get_body(first(@main i * sum(a, sum(b, A(a, b) * i * j)) f ctx))
    @test get_body(f2) == subst(get_body(f1), var(:k, N()), mul(var(:i, N()), var(:j, N())))

    # call substitution

    f1 = get_body(first(@main A(i, j) f ctx))
    old = get_body(f1)
    new = get_body(first(@pct f ctx A(j, k)))
    @test new == subst(get_body(f1), old, new)
end

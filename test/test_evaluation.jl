using PCT, Test

@testset "subst: free and dummy variables" begin
    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> R
        end
        (A::S, i::I, j::I) -> _
    end

    f1 = @pct f ctx A(i, j)
    vars = variables(f1)
    @test all(t -> t in vars, [var(:A, ctx[:S]), var(:i, I()), var(:j, I())])

    f1 = @pct f ctx sum(a, A(a, j))
    vars = variables(f1)
    @test var(:a, Z()) in vars

    # Dummy variables
    _, dummies = free_and_dummy(f1)
    @test all(t -> t in dummies, [var(:A, ctx[:S]), var(:i, I()), var(:j, I()), var(:a, Z())])

    # Contains name
    @test all(t -> contains_name(f1, t), [:i, :j, :A, :a])
end

@testset "substitution" begin
    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> R
        end
        (A::S, i::I, j::I, k::I, l::I) -> _
    end

    # simple substitution
    f1 = @pct f ctx A(i, j)
    f2 = @pct f ctx A(A(i, j), j)
    @test get_body(f2) == subst(get_body(f1), var(:i, I()), get_body(f1))

    # try to substituting a dummy variable
    f1 = @pct f ctx sum(a, A(a, j))
    @test get_body(f1) == subst(get_body(f1), var(:a, I()), var(:i, I()))

    f1 = @pct f ctx i * sum(i, A(i, j))
    f2 = @pct f ctx k * sum(i, A(i, j))
    @test get_body(f2) == subst(get_body(f1), var(:i, I()), var(:k, I()))

    f1 = @pct f ctx (a::I) -> A(a, j)
    @test get_body(f1) == subst(get_body(f1), var(:a, I()), var(:i, I()))

    # Resolving conflict

    f1 = @pct f ctx k * sum(i, A(i, j))
    f2 = @pct f ctx k * sum(a, A(a, i))
    @test get_body(f2) == subst(get_body(f1), var(:j, I()), var(:i, I()))

    f1 = @pct f ctx i * sum(i, sum(j, A(i, j) * k))
    f2 = @pct f ctx i * sum(a, sum(b, A(a, b) * i * j))
    @test get_body(f2) == subst(get_body(f1), var(:k, I()), mul(var(:i, I()), var(:j, I())))

    # call substitution

    f1 = @pct f ctx A(i, j)
    old = get_body(f1)
    new = get_body(@pct f ctx A(j, k))
    @test new == subst(get_body(f1), old, new)

    #= f1 = @pct f ctx A(i, j)
    old = get_body(@pct f ctx A(k, l))
    new = get_body(@pct f ctx A(i, j))
    result = get_body(@pct f ctx delta(j, l, delta(i, k, A(i, j))) + delta_not(j, l, delta_not(i, k, A(k, l))))
    @test result == subst(get_body(f1), old, new) =#

end

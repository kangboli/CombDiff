@testset "neighbors: constraction" begin

    f, ctx = @pct begin
        @domain I1 begin 
            base=I
            lower = -N
            upper = N
            symmetric=true
        end

        @space S begin
            type = (I1, I1) -> R
        end
        (A::S, i::I1, j::I1, N::I) -> _
    end
    
    # sum_ex
    #= f1 = @pct f ctx sum(a, sum(b, a * b))
    f2 = @pct f ctx sum(b, sum(a, a * b))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#
    # sum_sym
    f1 = @pct f ctx sum(a::I1, A(a, a))
    f2 = @pct f ctx sum(a::I1, A(-a, -a))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1); settings=symmetry_settings))

    # sum_mul    
    f1 = @pct f ctx sum(a::I1, i)
    f2 = @pct f ctx (N + (-1 * -1 * N)) * i
    k = nodes(PCT.neighbors(get_body(f1))) |> first
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1 = @pct f ctx sum(a::I1, 0)
    f2 = @pct f ctx 0
    @test f1 == f2

    # Delta contractions!
    f1 = @pct f ctx sum(a, delta(a, i, A(a, i)))
    f2 = @pct f ctx A(i, i)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1 = @pct f ctx sum(a::I1, delta(a, i, delta(a, j, A(a, j))))
    f2 = @pct f ctx delta(i, j, A(i, j))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # sum_dist
    f1 = @pct f ctx sum(a, a + a * j)
    f2 = @pct f ctx sum(a, a) + sum(a, a * j)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # sum_out
    f1 = @pct f ctx sum(a, a * j * i)
    f2 = @pct f ctx j * i * sum(a, a)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1); settings=custom_settings(:clench_sum=>true)))

    # sub PCT.neighbors
    f1 = @pct f ctx sum(a, a * a * i)
    f2 = @pct f ctx sum(a, a^(1+1) * i)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))
end

@testset "neighbors: constraction" begin

    M = 10
    f, ctx = @comb begin
        @domain I1 begin
            base = I
            lower = -M
            upper = M
            symmetric = true
        end

        @space S begin
            type = (I1, I1) -> R
        end
        (A::S, i::I1, j::I1) -> _
    end

    # sum_ex
    #= f1 = @pct f ctx sum(a, sum(b, a * b))
    f2 = @pct f ctx sum(b, sum(a, a * b))
    @test get_body(f2) in CombDiff.nodes(PCT.neighbors(get_body(f1))) =#
    # sum_sym
    f1 = get_body(first(@main sum(a::I1, A(a, a)) f ctx))
    f2 = get_body(first(@main sum(a::I1, A(-a, -a)) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1); settings=symmetry_settings()))

    # sum_mul    
    f1 = get_body(first(@main sum(a::I1, i) f ctx))
    f2 = get_body(first(@main (M + (-1 * -1 * M)) * i f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1 = get_body(first(@main sum(a::I1, 0) f ctx))
    f2 = get_body(first(@main 0 f ctx))
    @test f1 == f2

    # Delta contractions!
    f, ctx = @comb begin
        (A::RM, i::N, j::N) -> _
    end
    f1 = get_body(first(@main sum(a, delta(a, i, A(a, i))) f ctx))
    f2 = get_body(first(@main A(i, i) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1 = get_body(first(@main sum(a::N, delta(a, i, delta(a, j, A(a, j)))) f ctx))
    f2 = get_body(first(@main delta(i, j, A(i, j)) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # sum_dist
    f1 = get_body(first(@main sum(a, a + a * j) f ctx))
    f2 = get_body(first(@main sum(a, a) + sum(a, a * j) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # sum_out
    f1 = get_body(first(@main sum(a, a * j * i) f ctx))
    f2 = get_body(first(@main j * i * sum(a, a) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1); settings=custom_settings(:clench_sum => true)))

    # sub CombDiff.neighbors
    f1 = get_body(first(@main sum(a, a * a * i) f ctx))
    f2 = get_body(first(@main sum(a, a^(1 + 1) * i) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))
end

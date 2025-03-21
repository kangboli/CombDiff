using CombDiff, Test

@testset "neighbors: primitive calls with symmetries" begin

    f, ctx = @comb begin
        @space S begin
            type = (N, N) -> R
            symmetries = (A -> (i, j) -> A(j, i),)
        end
        (A::S, i::N, j::N) -> _
    end

    f1 = get_body(first(@main A(i, j) f ctx))
    f2 = get_body(first(@main A(j, i) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1); settings=symmetry_settings()))

    f, ctx = @comb begin
        @space H begin
            type = (N, N) -> C
            symmetries = (A -> (i, j) -> A(j, i)',)
        end
        (A::H, i::N, j::N) -> _
    end

    f1 = get_body(first(@main A(i, j) f ctx))
    f2 = get_body(first(@main A(j, i)' f ctx))

    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1); settings=symmetry_settings()))

    f, ctx = @comb begin
        @space T begin
            type = (N, N, N, N) -> C
            symmetries = (
                t -> (i, j, k, l) -> t(j, i, k, l),
                t -> (i, j, k, l) -> t(i, j, l, k),
                t -> (i, j, k, l) -> t(k, l, i, j),
            )
        end
        (T::T, i::N, j::N, p::N, q::N) -> _
    end

    f1 = get_body(first(@main T(i, j, p, q) f ctx))
    f2 = get_body(first(@main T(j, i, p, q) f ctx))
    f3 = get_body(first(@main T(i, j, q, p) f ctx))
    f4 = get_body(first(@main T(p, q, i, j) f ctx))
    @test all(f -> get_body(f) in CombDiff.nodes(CombDiff.neighbors(get_body(f1); settings=symmetry_settings())), [f2, f3, f4])


    # Composite primitive calls.
    f, ctx = @comb begin
        @space S begin
            type = (N, N) -> N
            symmetries = (A -> (i, j) -> -A(j, i),)
        end
        (A::S, B::S, i::N, j::N) -> _
    end

    f1 = get_body(first(@main A(i, B(i, j)) f ctx))
    f2 = get_body(first(@main -A(B(i, j), i) f ctx))
    f3 = get_body(first(@main A(i, -B(j, i)) f ctx))

    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1); settings=symmetry_settings()))
    @test get_body(f3) in CombDiff.nodes(CombDiff.neighbors(get_body(f1); settings=symmetry_settings()))
end

@testset "neighbors: addition" begin
    f, ctx = @comb begin
        (i::N, j::N, k::N) -> _
    end

    # GCD edges
    #= f1 = @pct f ctx i + i
    f2 = @pct f ctx i * (1 + 1)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    f1 = get_body(first(@main i + i * j f ctx))
    f2 = get_body(first(@main i * (1 + j) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i * k + i * j
    f2, _ = @pct f ctx i * (k + j)
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i * k + i * j * k
    f2, _ = @pct f ctx i * k * (j + 1)
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    #= # add-sum edges
    f1 = @pct f ctx sum(a, a * i) + sum(a, a * j)
    f2 = @pct f ctx sum(a, a * i + a * j)
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    #= f1 = @pct f ctx sum(a, a * i) + sum(b, b * j)
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    # add-delta edges

    f1, _ = @pct f ctx delta(i, j, k * i) + delta(i, j, k * j)
    f2, _ = @pct f ctx delta(i, j, k * i + k * j)
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # add-const CombDiff.neighbors

    #= f1 = @pct f ctx 2 + 3
    f2 = @pct f ctx 5
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    #= f1 = @pct f ctx 3 + i + j + 2
    f2 = @pct f ctx i + j + 5
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    # sub CombDiff.neighbors
    f, ctx = @comb begin
        @space S begin
            type = (N, N) -> C
            symmetries = (A -> (i, j) -> A(j, i),)
        end

        (A::S, i::N, j::N) -> _
    end

    f1 = get_body(first(@main A(i, j) + A(i, j) f ctx))
    f2 = get_body(first(@main A(i, j) + A(j, i) f ctx))
    @test get_body(f1) in CombDiff.nodes(CombDiff.neighbors(get_body(f2); settings=symmetry_settings()))
end

@testset "neighbors: multiplication" begin
    f, ctx = @comb (i::N, j::N, k::N) -> _

    #= # dist CombDiff.neighbors
    f1 = @pct f ctx i * (j + k)
    f2 = @pct f ctx (i * j) + (i * k)
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    #= f1 = @pct f ctx (i + 1) * (j + 1)
    f2 = @pct f ctx i * (j + 1) + j + 1
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    # swallow CombDiff.neighbors

    f1 = get_body(first(@main i * delta(j, k, j * k) f ctx))
    f2 = get_body(first(@main delta(j, k, i * j * k) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1 = get_body(first(@main i * j * delta(j, k, j * k) f ctx))
    f2 = get_body(first(@main delta(j, k, j * i * j * k) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # mul_add CombDiff.neighbors
    f1 = get_body(first(@main i * i * i f ctx))
    f2 = get_body(first(@main i^(1 + 1) * i f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1 = get_body(first(@main i * i^2 * j f ctx))
    f2 = get_body(first(@main i^(1 + 2) * j f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1 = get_body(first(@main i^j * i^k f ctx))
    f2 = get_body(first(@main i^(j + k) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # mul_prod CombDiff.neighbors
    #=
        f1 = @pct f ctx prod(a, i * a) * prod(a, j * a) * k
        f2 = @pct f ctx prod(a, i * j * a * a) * k
        @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    # prod_const CombDiff.neighbors
    #= f1 = @pct f ctx 2 * 3
    f2 = @pct f ctx 6
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1 = @pct f ctx i * 2 * 3 * j
    f2 = @pct f ctx 6 * i * j
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#
end

@testset "neighbors: monomial" begin
    # sum_mul CombDiff.neighbors
    f, ctx = @pct (i::N, j::N, k::N) -> _

    f1 = get_body(first(@main i^(sum(a, a * j)) f ctx))
    f2 = get_body(first(@main prod(a, i^(a * j)) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # add_mul CombDiff.neighbors

    f1 = get_body(first(@main i^(j + k) f ctx))
    f2 = get_body(first(@main i^j * i^k f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    f1 = get_body(first(@main i^(j + k) * i f ctx))
    f2 = get_body(first(@main i^j * i^k * i f ctx))
    f3 = get_body(first(@main i^(j + k + 1) f ctx))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))
    @test get_body(f3) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))
end

#= @testset "Product Neighbors" begin
    f, ctx = @pct begin
        @domain I1 I -N N

        @space S begin
            type = (I1, I1) -> R
        end
        (A::S, i::I1, j::I1, N::I) -> _
    end

    # prod_ex CombDiff.neighbors
    f1 = @pct f ctx prod(a, prod(b, a * b))
    f2 = @pct f ctx prod(b, prod(a, a * b))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # prod_sym CombDiff.neighbors
    f1 = @pct f ctx prod(a::I1, a + i)
    f2 = @pct f ctx prod(a::I1, -a + i)
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # prod_of_zeros
    f1 = @pct f ctx prod(a, 0)
    f2 = @pct f ctx 0
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # prod_of_ones
    f1 = @pct f ctx prod(a, 1)
    f2 = @pct f ctx 1
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # prod_power
    f1 = @pct f ctx prod(a::I1, i)
    f2 = @pct f ctx (i * (N + (-1*-1*N)))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # prod_dist
    f1 = @pct f ctx prod(a, a * A(a, i))
    f2 = @pct f ctx prod(a, a) * prod(a, A(a, i))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # prod_sum
    f1 = @pct f ctx prod(a, j^(a+i))
    f2 = @pct f ctx j^(sum(a, a+i))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))
end
 =#
@testset "neighbors: delta" begin
    f, ctx = @comb begin
        @space S begin
            type = (N, N) -> R
        end
        (A::S, i::N, j::N, p::N, q::N) -> _
    end

    # delta-ex
    #= f1 = get_body(first(@main delta(i, j, delta(p, q, A(i, j))) f ctx ))
    f2 = get_body(first(@main delta(p, q, delta(i, j, A(i, j))) f ctx ))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1))) =#

    # double-delta
    f1 = get_body(first(@main delta(i, j, delta(j, i, A(i, j))) f ctx ))
    f2 = get_body(first(@main delta(i, j, A(i, j)) f ctx ))
    @test get_body(f2) in CombDiff.nodes(CombDiff.neighbors(get_body(f1)))

    # delta-id
    f1 = get_body(first(@main delta(i, i, A(i, j)) f ctx ))
    f2 = get_body(first(@main A(i, j) f ctx ))
    @test f2 == f1
end

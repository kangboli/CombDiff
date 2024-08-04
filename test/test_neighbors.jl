using CombDiff, Test

@testset "neighbors: primitive calls with symmetries" begin

    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> R
            symmetries = (((2, 1), :id),)
        end
        (A::S, i::I, j::I) -> _
    end

    f1, _ = @pct f ctx A(i, j)
    f2, _ = @pct f ctx A(j, i)

    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1); settings=symmetry_settings))

    f, ctx = @pct begin
        @space H begin
            type = (I, I) -> C
            symmetries = (((2, 1), :conj),)
        end
        (A::H, i::I, j::I) -> _
    end

    f1, _ = @pct f ctx A(i, j)
    f2, _ = @pct f ctx A(j, i)'

    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1); settings=symmetry_settings))

    f, ctx = @pct begin
        @space T begin
            type = (I, I, I, I) -> C
            symmetries = (((2, 1, 3, 4), :id), ((1, 2, 4, 3), :id), ((3, 4, 1, 2), :id))
        end
        (T::T, i::I, j::I, p::I, q::I) -> _
    end

    f1, _ = @pct f ctx T(i, j, p, q)
    f2, _ = @pct f ctx T(j, i, p, q)
    f3, _ = @pct f ctx T(i, j, q, p)
    f4, _ = @pct f ctx T(p, q, i, j)
    @test all(f -> get_body(f) in nodes(PCT.neighbors(get_body(f1); settings=symmetry_settings)), [f2, f3, f4])


    # Composite primitive calls.
    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> I
            symmetries = (((2, 1), :neg),)
        end
        (A::S, B::S, i::I, j::I) -> _
    end

    f1, _ = @pct f ctx A(i, B(i, j))
    f2, _ = @pct f ctx -A(B(i, j), i)
    f3, _ = @pct f ctx A(i, -B(j, i))

    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1); settings=symmetry_settings))
    @test get_body(f3) in nodes(PCT.neighbors(get_body(f1); settings=symmetry_settings))
end

@testset "neighbors: addition" begin
    f, ctx = @pct begin
        (i::I, j::I, k::I) -> _
    end

    # GCD edges
    #= f1 = @pct f ctx i + i
    f2 = @pct f ctx i * (1 + 1)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    f1, _ = @pct f ctx i + i * j
    f2, _ = @pct f ctx i * (1 + j)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i * k + i * j
    f2, _ = @pct f ctx i * (k + j)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i * k + i * j * k
    f2, _ = @pct f ctx i * k * (j + 1)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    #= # add-sum edges
    f1 = @pct f ctx sum(a, a * i) + sum(a, a * j)
    f2 = @pct f ctx sum(a, a * i + a * j)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    #= f1 = @pct f ctx sum(a, a * i) + sum(b, b * j)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    # add-delta edges

    f1, _ = @pct f ctx delta(i, j, k * i) + delta(i, j, k * j)
    f2, _ = @pct f ctx delta(i, j, k * i + k * j)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # add-const PCT.neighbors

    #= f1 = @pct f ctx 2 + 3
    f2 = @pct f ctx 5
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    #= f1 = @pct f ctx 3 + i + j + 2
    f2 = @pct f ctx i + j + 5
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    # sub PCT.neighbors
    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> C
            symmetries = (((2, 1), :id),)

        end

        (A::S, i::I, j::I) -> _
    end

    f1, _ = @pct f ctx A(i, j) + A(i, j)
    f2, _ = @pct f ctx A(i, j) + A(j, i)
    @test get_body(f1) in nodes(PCT.neighbors(get_body(f2); settings=symmetry_settings))
end

@testset "neighbors: multiplication" begin
    f, ctx = @pct (i::I, j::I, k::I) -> _

    #= # dist PCT.neighbors
    f1 = @pct f ctx i * (j + k)
    f2 = @pct f ctx (i * j) + (i * k)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    #= f1 = @pct f ctx (i + 1) * (j + 1)
    f2 = @pct f ctx i * (j + 1) + j + 1
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    # swallow PCT.neighbors

    f1, _ = @pct f ctx i * delta(j, k, j * k)
    f2, _ = @pct f ctx delta(j, k, i * j * k)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i * j * delta(j, k, j * k)
    f2, _ = @pct f ctx delta(j, k, j * i * j * k)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # mul_add PCT.neighbors
    f1, _ = @pct f ctx i * i * i
    f2, _ = @pct f ctx i^(1 + 1) * i
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i * i^2 * j
    f2, _ = @pct f ctx i^(1 + 2) * j
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i^j * i^k
    f2, _ = @pct f ctx i^(j + k)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # mul_prod PCT.neighbors
#=
    f1 = @pct f ctx prod(a, i * a) * prod(a, j * a) * k
    f2 = @pct f ctx prod(a, i * j * a * a) * k
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#

    # prod_const PCT.neighbors
    #= f1 = @pct f ctx 2 * 3
    f2 = @pct f ctx 6
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1 = @pct f ctx i * 2 * 3 * j
    f2 = @pct f ctx 6 * i * j
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1))) =#
end

@testset "neighbors: monomial" begin
    # sum_mul PCT.neighbors
    f, ctx = @pct (i::I, j::I, k::I) -> _

    f1, _ = @pct f ctx i^(sum(a, a * j))
    f2, _ = @pct f ctx prod(a, i^(a * j))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # add_mul PCT.neighbors

    f1, _ = @pct f ctx i^(j + k)
    f2, _ = @pct f ctx i^j * i^k
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    f1, _ = @pct f ctx i^(j + k) * i
    f2, _ = @pct f ctx i^j * i^k * i
    f3, _ = @pct f ctx i^(j + k + 1)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))
    @test get_body(f3) in nodes(PCT.neighbors(get_body(f1)))
end

#= @testset "Product Neighbors" begin
    f, ctx = @pct begin
        @domain I1 I -N N

        @space S begin
            type = (I1, I1) -> R
        end
        (A::S, i::I1, j::I1, N::I) -> _
    end

    # prod_ex PCT.neighbors
    f1 = @pct f ctx prod(a, prod(b, a * b))
    f2 = @pct f ctx prod(b, prod(a, a * b))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # prod_sym PCT.neighbors
    f1 = @pct f ctx prod(a::I1, a + i)
    f2 = @pct f ctx prod(a::I1, -a + i)
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # prod_of_zeros
    f1 = @pct f ctx prod(a, 0)
    f2 = @pct f ctx 0
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # prod_of_ones
    f1 = @pct f ctx prod(a, 1)
    f2 = @pct f ctx 1
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # prod_power
    f1 = @pct f ctx prod(a::I1, i)
    f2 = @pct f ctx (i * (N + (-1*-1*N)))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # prod_dist
    f1 = @pct f ctx prod(a, a * A(a, i))
    f2 = @pct f ctx prod(a, a) * prod(a, A(a, i))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # prod_sum
    f1 = @pct f ctx prod(a, j^(a+i))
    f2 = @pct f ctx j^(sum(a, a+i))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))
end
 =#
@testset "neighbors: delta" begin
    f, ctx = @pct begin
        @space S begin
            type=(I, I) -> R
        end
        (A::S, i::I, j::I, p::I, q::I) -> _
    end

    # delta-ex
    f1, _ = @pct f ctx delta(i, j, delta(p, q, A(i, j)))
    f2, _ = @pct f ctx delta(p, q, delta(i, j, A(i, j)))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # double-delta
    f1, _ = @pct f ctx delta(i, j, delta(j, i, A(i, j)))
    f2, _ = @pct f ctx delta(i, j, A(i, j))
    @test get_body(f2) in nodes(PCT.neighbors(get_body(f1)))

    # delta-id
    f1, _ = @pct f ctx delta(i, i, A(i, j)) 
    f2, _ = @pct f ctx A(i, j)
    @test f2 == f1
end

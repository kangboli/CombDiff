using PCT, Test

@testset "Primitive call & symmetries" begin

    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> R
            symmetries = (((2, 1), :id),)
        end

        (A::S, i::I, j::I) -> _
    end

    f1 = @pct f ctx A(i, j)
    f2 = @pct f ctx A(j, i)

    @test fc(f2) in nodes(neighbors(fc(f1)))

    f, ctx = @pct begin
        @space H begin
            type = (I, I) -> C
            symmetries = (((2, 1), :conj),)
        end

        (A::H, i::I, j::I) -> _
    end

    f1 = @pct f ctx A(i, j)
    f2 = @pct f ctx A(j, i)'

    @test fc(f2) in nodes(neighbors(fc(f1)))

    f, ctx = @pct begin
        @space T begin
            type = (I, I, I, I) -> C
            symmetries = (((2, 1, 3, 4), :id), ((1, 2, 4, 3), :id), ((3, 4, 1, 2), :id))
        end

        (T::T, i::I, j::I, p::I, q::I) -> _
    end

    f1 = @pct f ctx T(i, j, p, q)
    f2 = @pct f ctx T(j, i, p, q)
    f3 = @pct f ctx T(i, j, q, p)
    f4 = @pct f ctx T(p, q, i, j)
    @test all(f -> fc(f) in nodes(neighbors(fc(f1))), [f2, f3, f4])


    # Composite primitive calls.
    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> I
            symmetries = (((2, 1), :neg),)
        end

        (A::S, B::S, i::I, j::I) -> _
    end
    f1 = @pct f ctx A(i, B(i, j))
    f2 = @pct f ctx -A(B(i, j), i)
    f3 = @pct f ctx A(i, -B(j, i))

    @test fc(f2) in nodes(neighbors(fc(f1)))
    @test fc(f3) in nodes(neighbors(fc(f1)))

end

@testset "Addition neighbors" begin
    f, ctx = @pct begin
        (i::I, j::I, k::I) -> _
    end

    # GCD edges
    f1 = @pct f ctx i + i
    f2 = @pct f ctx i * (1 + 1)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i + i * j
    f2 = @pct f ctx i * (1 + j)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i * k + i * j
    f2 = @pct f ctx i * (k + j)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i * k + i * j * k
    f2 = @pct f ctx i * k * (j + 1)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # add-sum edges

    f1 = @pct f ctx sum(a, a * i) + sum(a, a * j)
    f2 = @pct f ctx sum(a, a * i + a * j)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx sum(a, a * i) + sum(b, b * j)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # add-delta edges

    f1 = @pct f ctx delta(i, j, k * i) + delta(i, j, k * j)
    f2 = @pct f ctx delta(i, j, k * i + k * j)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # add-const neighbors

    f1 = @pct f ctx 2 + 3
    f2 = @pct f ctx 5
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx 3 + i + j + 2
    f2 = @pct f ctx i + j + 5
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # sub neighbors
    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> C
            symmetries = (((2, 1), :id),)

        end

        (A::S, i::I, j::I) -> _
    end

    f1 = @pct f ctx A(i, j) + A(i, j)
    f2 = @pct f ctx A(i, j) + A(j, i)
    @test fc(f2) in nodes(neighbors(fc(f1)))
end

@testset "Multiplication Neighbors" begin
    f, ctx = @pct (i::I, j::I, k::I) -> _

    # dist neighbors
    f1 = @pct f ctx i * (j + k)
    f2 = @pct f ctx (i * j) + (i * k)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx (i + 1) * (j + 1)
    f2 = @pct f ctx i * (j + 1) + j + 1
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # swallow neighbors

    f1 = @pct f ctx i * delta(j, k, j * k)
    f2 = @pct f ctx delta(j, k, i * j * k)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i * j * delta(j, k, j * k)
    f2 = @pct f ctx delta(j, k, j * i * j * k)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # mul_add neighbors
    f1 = @pct f ctx i * i * i
    f2 = @pct f ctx i^(1 + 1) * i
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i * i^2 * j
    f2 = @pct f ctx i^(1 + 2) * j
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i^j * i^k
    f2 = @pct f ctx i^(j + k)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # mul_prod neighbors

    f1 = @pct f ctx prod(a, i * a) * prod(a, j * a) * k
    f2 = @pct f ctx prod(a, i * j * a * a) * k
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # prod_const neighbors
    f1 = @pct f ctx 2 * 3
    f2 = @pct f ctx 6
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i * 2 * 3 * j
    f2 = @pct f ctx 6 * i * j
    @test fc(f2) in nodes(neighbors(fc(f1)))
end

@testset "Monomial Neighbors" begin
    # sum_mul neighbors
    f, ctx = @pct (i::I, j::I, k::I) -> _

    f1 = @pct f ctx i^(sum(a, a * j))
    f2 = @pct f ctx prod(a, i^(a * j))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # add_mul neighbors

    f1 = @pct f ctx i^(j + k)
    f2 = @pct f ctx i^j * i^k
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx i^(j + k) * i
    f2 = @pct f ctx i^j * i^k * i
    f3 = @pct f ctx i^(j + k + 1)
    @test fc(f2) in nodes(neighbors(fc(f1)))
    @test fc(f3) in nodes(neighbors(fc(f1)))

end

@testset "Constraction Neighbors" begin
    # sum_ex

    f, ctx = @pct begin
        @domain I1 I -N N

        @space S begin
            type = (I1, I1) -> R
        end
        (A::S, i::I1, j::I1, N::I) -> _
    end
    f1 = @pct f ctx sum(a, sum(b, a * b))
    f2 = @pct f ctx sum(b, sum(a, a * b))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # sum_sym

    f1 = @pct f ctx sum(a::I1, A(a, a))
    f2 = @pct f ctx sum(a::I1, A(-a, -a))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # sum_mul    
    f1 = @pct f ctx sum(a::I1, i)
    f2 = @pct f ctx (N + (-1 * -1 * N)) * i
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx sum(a::I1, 0)
    f2 = @pct f ctx 0
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # Delta contractions!
    f1 = @pct f ctx sum(a, delta(a, i, A(a, i)))
    f2 = @pct f ctx A(i, i)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    f1 = @pct f ctx sum(a::I1, delta(a, i, delta(a, j, A(a, j))))
    f2 = @pct f ctx delta(i, j, A(i, j))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # sum_dist
    f1 = @pct f ctx sum(a, a + a * j)
    f2 = @pct f ctx sum(a, a) + sum(a, a * j)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # sum_out
    f1 = @pct f ctx sum(a, a * j * i)
    f2 = @pct f ctx j * i * sum(a, a)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # sub nodes
    f1 = @pct f ctx sum(a, a * a * i)
    f2 = @pct f ctx sum(a, a^(1+1) * i)
    @test fc(f2) in nodes(neighbors(fc(f1)))

end

@testset "Product Neighbors" begin
    f, ctx = @pct begin
        @domain I1 I -N N

        @space S begin
            type = (I1, I1) -> R
        end
        (A::S, i::I1, j::I1, N::I) -> _
    end

    # prod_ex neighbors
    f1 = @pct f ctx prod(a, prod(b, a * b))
    f2 = @pct f ctx prod(b, prod(a, a * b))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # prod_sym neighbors
    f1 = @pct f ctx prod(a::I1, a + i)
    f2 = @pct f ctx prod(a::I1, -a + i)
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # prod_of_zeros
    f1 = @pct f ctx prod(a, 0)
    f2 = @pct f ctx 0
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # prod_of_ones
    f1 = @pct f ctx prod(a, 1)
    f2 = @pct f ctx 1
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # prod_power
    f1 = @pct f ctx prod(a::I1, i)
    f2 = @pct f ctx (i * (N + (-1*-1*N)))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # prod_dist
    f1 = @pct f ctx prod(a, a * A(a, i))
    f2 = @pct f ctx prod(a, a) * prod(a, A(a, i))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # prod_sum
    f1 = @pct f ctx prod(a, j^(a+i))
    f2 = @pct f ctx j^(sum(a, a+i))
    @test fc(f2) in nodes(neighbors(fc(f1)))
end

@testset "Delta neighbors" begin
    f, ctx = @pct begin
        @space S begin
            type=(I, I) -> R
        end
        (A::S, i::I, j::I, p::I, q::I) -> _
    end

    # delta-ex
    f1 = @pct f ctx delta(i, j, delta(p, q, A(i, j)))
    f2 = @pct f ctx delta(p, q, delta(i, j, A(i, j)))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # double-delta
    f1 = @pct f ctx delta(i, j, delta(j, i, A(i, j)))
    f2 = @pct f ctx delta(i, j, A(i, j))
    @test fc(f2) in nodes(neighbors(fc(f1)))

    # delta-id
    f1 = @pct f ctx delta(i, i, A(i, j)) 
    f2 = @pct f ctx A(i, j)
    @test fc(f2) in nodes(neighbors(fc(f1)))
end

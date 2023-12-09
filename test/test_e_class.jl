using PCT, Test


#= @testset "e_class: primitive calls and symmetries" begin
    f, ctx = @pct begin
        @space S begin
            type = (I, I) -> R
            symmetries = (((2, 1), :id),)
        end

        (A::S, i::I, j::I) -> _
    end

    f1 = @pct f ctx A(i, j)
    f2 = @pct f ctx A(j, i)

    @test f1 == f2

    f, ctx = @pct begin
        @space H begin
            type = (I, I) -> C
            symmetries = (((2, 1), :conj),)
        end

        (A::H, i::I, j::I) -> _
    end

    f1 = @pct f ctx A(i, j)
    f2 = @pct f ctx A(j, i)'

    @test f1 == f2


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

    @test f1 == f2 == f3 == f4

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

    @test f1 == f2 == f3
end =#

@testset "Contraction and Products" begin

    f1, _ = @pct sum(a, 0)
    f2, _ = @pct  0
    @test f1 == f2

    #= # prod_of_zeros
    f1 = @pct f ctx prod(a, 0)
    f2 = @pct f ctx 0
    @test f1 == f2

    # prod_of_ones
    f1 = @pct f ctx prod(a, 1)
    f2 = @pct f ctx 1
    @test f1 == f2 =#
end

#= @testset "Delta E-Class" begin
    f, ctx = @pct begin
        @space S begin
            type=(I, I) -> R
        end
        (A::S, i::I, j::I, p::I, q::I) -> _
    end

    # delta-ex
    f1 = @pct f ctx delta((i, j), (p, q), A(i, j))
    f2 = @pct f ctx delta((p, q), (i, j), A(i, j))
    @test f1 == f2

    # double-delta
    f1 = @pct f ctx delta((i, j), (j, i), A(i, j))
    f2 = @pct f ctx delta(i, j, A(i, j))
    @test f1 == f2

    # delta-id
    f1 = @pct f ctx delta(i, i, A(i, j)) 
    f2 = @pct f ctx A(i, j)
    @test f1 == f2
end =#

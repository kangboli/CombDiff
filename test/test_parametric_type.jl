using CombDiff


@test_throws ErrorException @main(:((n::N) -> (i::N{n}) -> (n::R) -> i))
@test_throws UndefVarError @main(:((n::N, i::N{n}) -> (n::R) -> i))

#=
_, ctx = @pct begin
    @domain I1{n} begin
        base = I
        lower = -n
        upper = n
    end

    @space M{m} begin
        type = (I1{m},) -> R
    end
end

@macroexpand @pct begin
    @domain I1{n} begin
        base = I
        lower = -n
        upper = n
    end

    @space M{m} begin
        type = (I1{m},) -> R
    end
end

f, _ = @comb :(
    begin
        mvp = {N}(A::RM{N}, v::RV{N}) -> (i::N{N}) -> sum((j::N{N}), A(i, j) * v(j))
        #= (M::N) -> (X::RM{M}, y::RM{M}) -> mvp(X, y) =#
    end
)

@macroexpand @comb :(
    (N_e::N) -> begin
        @domain occ N{N_e}
    end
) =#

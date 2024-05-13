using PCT

f, _ = @pct begin
    mvp = (A::RM, x::RV) -> (i::N) -> sum(j, A(i, j) * x(j))
    vip = (x::RV, y::RV) -> sum(i, x(i) * y(i))
    (batch::RV, Relu::RF) ->
        pullback((t_2::RM, w::RV, t_1::RM) ->
            (((x::RV) -> mvp(t_1, x)) ▷
             ((x::RV) -> (i::N) -> Relu(x(i))) ▷
             ((x::RV) -> mvp(t_2, x)) ▷
             ((x::RV) -> (i::N) -> Relu(x(i))) ▷
             ((x::RV) -> vip(x, w)))(
                batch
            ))
end

# get_body(get_body(get_body(get_body(get_body(f))))) |> decompose |> pp |> eval_all

df = vdiff(f)
edf = eval_all(eval_pullback(deprimitize(eval_all(df))))
bedf = blaserize(edf)


f, ctx = @pct begin
    @size N M N K
    @domain T N 1 M

    mvp = (A::RM, x::RV) -> (i::N) -> sum(j, A(i, j) * x(j))
    vip = (x::RV, y::RV) -> sum(i, x(i) * y(i))

    (batch::RV, Relu::RF) ->
        pullback((t_2::RM, w::RV, t_1::RM) ->
            (((x::RV) -> mvp(t_1, x)) ▷
             ((x::RV) -> (i::N) -> Relu(x(i))) ▷
             ((x::RV) -> mvp(t_2, x)) ▷
             ((x::RV) -> (i::N) -> Relu(x(i))) ▷
             ((x::RV) -> vip(x, w)))(
                batch
            ))
end


Meta.parse("
@domain T{M, K} begin
    base=N
    lower=1
    upper=M
end
") |> Meta.dump


Meta.parse("
@space T{M, K} begin
    type=(N{M}, N{K}) -> R
end
") |> Meta.dump

@macroexpand @pct begin
    @domain T{M} begin
        type = N
        lower = 1
        upper = M
    end
    @space G{K} begin
        type = (T{K}, T{K}) -> R
    end
end

_, T = @pct begin
    @size N K

    @domain T{M} begin
        type = N
        lower = 1
        upper = M
    end

    (i::N{K}) -> i + 1
end

@macroexpand @pct begin
    @size N K

    @domain T{M} begin
        type = N
        lower = 1
        upper = M
    end

    (i::N{K}) -> i + 1
end

Meta.parse(
    "
    {R, S}(a::R, b::S) -> a + b
    ") |> Meta.dump

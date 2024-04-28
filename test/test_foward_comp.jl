using PCT

f, _ = @pct begin
    @space T begin
        type=(N, )->N
    end
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
        type=N
        lower=1
        upper=M
    end
    @space G{K}  begin
        type=(T{K}, T{K}) -> R
    end
end


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


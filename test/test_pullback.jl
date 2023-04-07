using PCT
ctx = @pct begin
    @space begin
        name=V
        type=(I,)->R
    end

    (x::V) -> _
end

f = @pct ctx sum(i, x(i) * x(i))

simplify(evaluate(evaluate_pullback(pullback(f)))) |> first

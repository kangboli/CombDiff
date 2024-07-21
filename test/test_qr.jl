f, _ = @pct begin
    (j::N) -> pullback((A::RM) -> let n = sum(i, A(i, j)^2)
    let v = (i::N) -> A(i, j) * n^(-0.5)
    (i::N, j::N) -> A(i, j) - v(i) * v(j)
    end
    end)
end

df = eval_pullback(eval_all(f))

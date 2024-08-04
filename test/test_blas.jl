using CombDiff
f, _ = @pct (A::RM, v::RV) -> sum((i::N, j::N), v(i) * A(i, j) * v(j))
bf = blaserize(f) |> first
codegen(bf)

f, _ = @pct (v::CV) -> 2 * sum((i::N), v(i)' * v(i))
bf = blaserize(f) |> first
codegen(bf)

f, _ = @pct (A::CM, v::CV) -> (j::N) -> sum((i::N), v(i)' * A(i, j))
bf = blaserize(f) |> first
codegen(bf)

f, _ = @pct (A::CM, v::CV) -> (i::N) -> sum((j::N), v(j)' * A(i, j))
bf = blaserize(f) |> first
codegen(bf)

f, _ = @pct (v::RV) -> sum((i::N), v(i) * v(i))
bf = blaserize(f) |> first
codegen(bf)

f, _ = @pct (A::CM, B::CM) -> (i::N, j::N) -> sum((k::N), A(i, k) * B(k, j))
bf = blaserize(f) |> first
codegen(bf)

f, _ = @pct (x::RV, p::RV, a::R) -> (i::N) -> x(i) + a * p(i)
bf = blaserize(f) |> first
codegen(bf)

f, _ = @pct (A::CM, B::CM) -> (i::N, j::N) -> sum((k::N), A(k, i)' * B(k, j))
bf = blaserize(f) |> first

f, _ = @pct (A::CM, B::CM) -> sum((i, j), A(i, j)' * B(i, j))
bf = blaserize(f) |> first

f, _ = @pct (A::CM, B::CM) -> sum((i, j), A(i, j) * B(i, j))
bf = blaserize(f) |> first


f, _ = @pct (A::RM, B::RM) -> (i::N) -> sum(j, A(i, j) * B(i, j))
bf = blaserize(f) |> first

f, _ = @pct (A::RM, B::RM) -> (i::N, j::N) -> sum((k::N), A(i, k) * B(k, j))
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)

f, _ = @pct (A::RM) -> (i::N, j::N) -> A(i, j)
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)

f, _ = @pct (A::RM, v::RV) -> (i::N) -> sum(j, A(i, j) * v(j)) 
blaserize(f)
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)

_, ctx = @pct begin
    @space T3 begin
        type=(N, N, N) -> R
    end
    @domain I1 begin
        base=N
        tensorize=false
    end
end

f, _ = @pct _ ctx (T::T3, x::RV) -> (i::I1) -> sum((j, k), T(i, j, k) * x(i) * x(j) * x(k))
blaserize(f)

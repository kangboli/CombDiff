using PCT
f, _ = @pct (A::RM, v::RV) -> sum((i::N, j::N), v(i) * A(i, j) * v(j))
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)

f, _ = @pct (v::RV) -> sum((i::N), v(i) * v(i))
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)

f, _ = @pct (A::RM, B::RM) -> (i::N, j::N) -> sum((k::N), A(i, k) * B(k, j))
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)

f, _ = @pct (A::RM) -> (i::N, j::N) -> A(i, j)
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)

f, _ = @pct (A::RM, v::RV) -> (i::N) -> sum(j, A(i, j) * v(j)) 
g = contraction_graph(get_body(f))
rewrite_degree_two_contraction!(g)




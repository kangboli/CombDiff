using CombDiff, Test

@pct (x::N) -> indicator(x, 4, x)

f, _ = @pct (i::N, j::N) -> vac_exp(:a(i) ∘ :a(i)')
f, _ = @pct (g::CM) -> sum((i, j), g(i, j) * vac_exp(:a(i) ∘ :a(j)'))

simplify(reduce_vac(f)) |> first

f, _ = @pct (N_o::N, g::CM) -> ((a::FField) -> sum((i, j), vac_exp(:II(g(i, j)) ∘ a(i) ∘ a(j)')))(
    (p::N) -> 𝕀(p, N_o, :b(p)') + 𝕀(N_o + 1, p, :c(p))
)

@macroexpand @pct (N_o::N, g::CM) -> ((a::FField) -> sum((i, j), vac_exp(:II(g(i, j)) ∘ a(i) ∘ a(j)')))(
    (p::N) -> 𝕀(p, N_o, :b(p)') + 𝕀(N_o + 1, p, :c(p))
)

f, _ = @pct (g::CM, i::N, j::N) -> g(i, j) * vac_exp(:a(i) ∘ :a(j)')

f, _ = @pct (i::N, j::N) -> vac_exp((:a(i) + :a(j)') ∘ (:a(j) + :a(i)'))

f, _ = @pct (i::N, j::N) -> vac_exp(i * :a(j))


f, _ = @pct (i::N, j::N) -> ((a::FField) -> a(i) ∘ a(j)')(:b)

# f, _ = @pct (N_o::N) -> ((c::FField) -> 𝕀 )
"""

"""


simplify(reduce_vac(f)) |> first

vacuum_exp(content(get_body(get_body(f))))
x, y = content(get_body(get_body(f)))
anti_commutator(x, y)

vacuum_exp([x, y])

f, _ = @pct (i::N, j::N) -> :a(i) ∘ :a(j)'
vacuum_exp(content(get_body(get_body(f))))

f, _ = @pct (i::N, j::N) -> :a(i) ∘ :b(j)'
vacuum_exp(content(get_body(get_body(f))))


f, _ = @pct (ϵ::RV) -> sum((i::N ∈ (1,  N)), ϵ(i) * (:a(i) ∘ :a(i)'))
vacuum_exp(f)

using CombDiff

fx, ctx = @pct begin
	@space T begin
		type = (I, I, I, I) -> C
		symmetries = (((2, 1, 4, 3), :conj), ((3, 4, 1, 2), :id))
	end
	(J::T) -> _ 
end

e2, _ = @pct fx ctx (N_o::N, v::T) -> ((a::FField) -> sum((i, j, k, l), vac_exp(:II(v(i, j, k, l)) ∘ a(i)' ∘ a(j)' ∘ a(l) ∘ a(k))))(
    (p::N) -> 𝕀(p, N_o, :b(p)') + 𝕀(N_o + 1, p, :c(p))
); e2

@profview g = simplify(eval_all(e2); settings=custom_settings(:logging=>false))

f, _ = @pct (N_o::N, g::CM) -> ((a::FField) -> 
    sum((i, j), vac_exp(:II(g(i, j)) ∘ a(i) ∘ a(j)')))(
    (p::N) -> 𝕀(p, N_o, :b(p)') + 𝕀(N_o + 1, p, :c(p))
); f

@profview g = f |> eval_all |> simplify |> first
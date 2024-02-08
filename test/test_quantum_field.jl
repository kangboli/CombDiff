using PCT, Test

f, _ = @pct (i::N) -> :a(i) ∘ :a(i)'
vacuum_exp(content(get_body(get_body(f))))
x, y = content(get_body(get_body(f)))
anti_commutator(x, y)

vacuum_exp([x, y])

f, _ = @pct (i::N, j::N) -> :a(i) ∘ :a(j)'
vacuum_exp(content(get_body(get_body(f))))

f, _ = @pct (i::N, j::N) -> :a(i) ∘ :b(j)'
vacuum_exp(content(get_body(get_body(f))))

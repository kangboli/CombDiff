using Test, PCT

f, _ = @pct (t::R) -> ((x::R) -> x + t) ∘ ((y::R) -> y + t)

f_decomp = decompose(f)
pp(f_decomp)

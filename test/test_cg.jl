
f, _ = @main (A::Sym, r::RV, p::RV, b::RV, x::RV) -> begin
    R = (x::RV) ->
        sum((i, j), 0.5 * x(i) * A(i, j) * x(j)) - sum(i, x(i) * b(i))
    pullback((alpha::R, beta::R) ->
        R((i::N) -> x(i) + alpha * (r(i) + beta * p(i))))
end

# Differentiate while keeping R intact
vdiff(f)

# Symbolic substitute R with its value before differentiating
vdiff(eval_all(CombDiff.strip_copy(f))) |> fast_symmetry_reduction |> blaserize


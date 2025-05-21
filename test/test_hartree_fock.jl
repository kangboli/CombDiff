using CombDiff, Test

# Encode the symmetries of ERI 
# as part of the type
_, ctx = @comb :(
    begin
        @space ERI begin
            type = (N, N, N, N) -> R
            symmetries = (
                J -> (j, i, b, a) -> J(i, j, a, b)',
                J -> (a, b, i, j) -> J(i, j, a, b))
        end
    end
)


# The Coulomb energy in Hartree Fock
coul, _ = @main :(
    (J::ERI) -> pullback((C::CM) ->
        sum((i, j, p, q, r, s), C(p, i)' * C(q, i) * C(r, j)' * C(s, j) *
                                J(p, q, r, s)))
) _ ctx


# Differentiate the energy and simplify based on the symmetries.
vdiff(coul) |> fast_symmetry_reduction 

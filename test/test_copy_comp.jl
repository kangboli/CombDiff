using Test, PCT

#= _, ctx = @pct begin
    @space begin
        type=(N,)->
    end
end =#

f, _ = @pct (m::R) -> (t::RV) -> (((x::R) -> x + t(1)) ∘ ((y::R) -> y + t(2)) ∘ ((z::R) -> z + t(3)))(m)

f_decomp = decompose(get_body(f))
eval_all(pp(f_decomp)) |> simplify |> first

f, _ = @pct (m::R) -> pullback((t_1::R, t_2::R) -> (((x::R) -> x + t_1) ∘ ((z::R) -> z + t_2))(m))

vdiff(f)

f_decomp = decompose(get_body(f))
eval_all(pp(f_decomp)) |> simplify |> first

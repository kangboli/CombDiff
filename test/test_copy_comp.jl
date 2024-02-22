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
f, _ = @pct (m::R) -> pullback((t_1::R, t_2::R, t_3::R) -> (((x::R) -> x + t_1) ∘ ((y::R) -> y + t_2) ∘ ((z::R) -> z + t_3))(m))

vdiff(f)

f_decomp = decompose(get_body(f))
eval_all(pp(f_decomp)) |> simplify |> first

f, _ = @pct (m::RM) -> let matmul = (A::RM, B::RM) -> (i::N, j::N) -> sum(n, A(i, n) * B(n, j))
    pullback((t_0::RV, t_1::RM, t_2::RM, t_3::RM) -> (
        ((x::RM) -> sum((i, j), t_0(i) * x(i, j))) ∘
        ((x::RM) -> matmul(t_1, x)) ∘
        ((y::RM) -> matmul(t_2, y)) ∘
        ((z::RM) -> matmul(t_3, z)))(m))
end

df = vdiff(f)

f, _ = @pct (m::RM) -> let
    mvp = (A::RM, x::RV) -> (i::N) -> sum(j, A(i, j) * x(j))
    vip = (x::RV, y::RV) -> sum(i, x(i) * y(i))
    pullback((t_1::RM, t_2::RM, t_3::RM, w::RV) -> (
        ((x::RM) -> vip(x, w)) ∘
        ((x::RM) -> mvp(t_3, x)) ∘
        ((x::RM) -> mvp(t_2, x)) ∘
        ((x::RV) -> mvp(t_1, x)))(m))
end

df = vdiff(f)

f, _ = @pct (m::RM) -> 
let mvp = (A::RM, x::RV) -> (i::N) -> sum(j, A(i, j) * x(j))
    vip = (x::RV, y::RV) -> sum(i, x(i) * y(i))
    pullback((t_1::RM, w::RV) -> (
        ((x::RV) -> vip(x, w)) ∘
        ((x::RV) -> mvp(t_1, x)))(m))
end
df = PCT.eval_pullback(f)
dfe = eval_all(df)

@macroexpand @pct (m::RM) -> 
let mvp = (A::RM, x::RV) -> (i::N) -> sum(j, A(i, j) * x(j))
    vip = (x::RV, y::RV) -> sum(i, x(i) * y(i))
    pullback((t_1::RM, w::RV) -> (
        ((x::RV) -> vip(x, w)) ∘
        ((x::RV) -> mvp(t_1, x)))(m))
end


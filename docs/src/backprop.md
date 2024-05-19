# Analytic Backpropagation

## Conjugate gradient 

```julia
f, _ = @pct (A::Sym, r::RV, p::RV, b::RV, x::RV) -> begin
    E = (x::RV) -> sum((i, j), 0.5 * x(i) * A(i, j) * x(j)) - sum(i, x(i) * b(i))
    pullback((α::R, β::R) -> E((i::N) -> x(i) + α * (r(i) + β * p(i))))
end; blaserize(f)
```

```math
\begin{aligned}
&\left(A, r, p, b, x\right) \mapsto \mathrm{let}\\
&\quad E = x \mapsto \left(-1.0\cdot x^{T}\cdot b+x^{T}\cdot A\cdot x\cdot 0.5\right)\\
&\quad \mathcal{P}\left(\left(α, β\right) \mapsto E\left(\left(x+α \cdot \left(r+β \cdot p\right)\right)\right)\right)\\
&\mathrm{end}
\end{aligned}
```

```julia
df = vdiff(f) |> blaserize 
```

```math
\begin{aligned}
&\left(A, r, p, b, x\right) \mapsto \mathrm{let}\\ 
&\quad E = x \mapsto \left(-1.0\cdot x^{T}\cdot b+x^{T}\cdot A\cdot x\cdot 0.5\right)\\
&\quad \left(α, β\right) \mapsto \left(\nabla \left(E\right)\left(\left(x+α \cdot \left(r+β \cdot p\right)\right)\right)^{T}\cdot \left(r+β \cdot p\right), \nabla \left(E\right)\left(\left(x+α \cdot \left(r+β \cdot p\right)\right)\right)^{T}\cdot p\cdot α\right)\\
&\mathrm{end}
\end{aligned}
```

```julia
df = redux(vdiff(eval_all(f)); settings=symmetry_settings) |> blaserize
```

```math
\left(A, r, p, b, x\right) \to \left(α, β\right) \to \left(\left(\left(r+β \cdot p\right)^{T}\cdot b+\left(x+α \cdot \left(r+β \cdot p\right)\right)^{T}\cdot A\cdot \left(r+β \cdot p\right)\right), α\cdot \left(b^{T}\cdot p+\left(x+α \cdot \left(r+β \cdot p\right)\right)^{T}\cdot A\cdot p\right)\right)
```

## Multi-layer perceptron

```julia
f, _ = @pct begin
    mvp = (A::RM, x::RV) -> (i::N) -> sum(j, A(i, j) * x(j))
    vip = (x::RV, y::RV) -> sum(i, x(i) * y(i))
    (batch::RV, Relu::RF) ->
        pullback((t_1::RM, t_2::RM, w::RV) ->
            (((x::RV) -> mvp(t_1, x)) ▷
             ((x::RV) -> (i::N) -> Relu(x(i))) ▷
             ((x::RV) -> mvp(t_2, x)) ▷
             ((x::RV) -> (i::N) -> Relu(x(i))) ▷
             ((x::RV) -> vip(x, w)))(
                batch
            ))
end;  print(pretty(f))
```

```txt
let 
    mvp = (A, x) -> (i) -> ∑((j), x(j)⋅A(i, j))
    vip = (x, y) -> ∑((i), x(i)⋅y(i))
    (batch, Relu) -> 𝒫((t_1, t_2, w) -> ((x) -> mvp(t_1, x) ▷
    (x) -> (i) -> Relu(x(i)) ▷
    (x) -> mvp(t_2, x) ▷
    (x) -> (i) -> Relu(x(i)) ▷
    (x) -> vip(x, w))(batch))
end
```

```julia
df = vdiff(f); print(pretty(df))
```

```txt
let 
    mvp = (A, x) -> (i) -> ∑((j), x(j)⋅A(i, j))
    vip = (x, y) -> ∑((i), x(i)⋅y(i))
    (batch, Relu) -> (t_1, t_2, w) -> let 
        %_y = mvp(t_1, batch)
        %_y_1 = (i) -> Relu(_y(i))
        %_y_2 = mvp(t_2, _y_1)
        %_y_3 = (i) -> Relu(_y_2(i))
        %_y_4 = vip(_y_3, w)
        %_l = 𝒫((_x_1) -> vip(_x_1, w))(_y_3, 1)
        %_l_1 = 𝒫((_x_1) -> (i) -> Relu(_x_1(i)))(_y_2, _l)
        %_l_2 = 𝒫((_x_1) -> mvp(t_2, _x_1))(_y_1, _l_1)
        %_l_3 = 𝒫((_x_1) -> (i) -> Relu(_x_1(i)))(_y, _l_2)
        𝒫((_z_1) -> mvp(_z_1, batch))(t_1, _l_3), 𝒫((_z_1) -> mvp(_z_1, _y_1))(t_2, _l_1), 𝒫((_z_1) -> vip(_y_3, _z_1))(w, 1)
    end
end
```

```julia
edf = eval_all(eval_pullback(deprimitize(eval_all(df))))
bedf = blaserize(edf)
print(pretty(bedf))
```

```txt
(batch, Relu) -> (t_1, t_2, w) -> let 
    %_y = t_1⋅batch
    %_y_1 = (i) -> Relu(_y(i))
    %_y_2 = t_2⋅_y_1
    %_y_3 = (i) -> Relu(_y_2(i))
    %_y_4 = wᵀ⋅_y_3
    %_l = w
    %_l_1 = (_d) -> _l(_d)⋅𝒫(Relu)(_y_2(_d), 1)
    %_l_2 = _l_1ᵀ⋅t_2
    %_l_3 = (_d) -> _l_2(_d)⋅𝒫(Relu)(_y(_d), 1)
    (_d, _d_1) -> _l_3(_d)⋅batch(_d_1), (_d, _d_1) -> _l_1(_d)⋅_y_1(_d_1), _y_3
end
```

## Optimal Control



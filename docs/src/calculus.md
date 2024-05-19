# Calculus of Variations

## $\langle \psi | H | \psi \rangle$

```julia
E, _ = @pct begin
    @space Hermitian begin
        type=(R, R)->C
        symmetries=(((2,1), :conj),)
    end
    (H::Hermitian) -> pullback((ψ::CF) -> ∑((x::R, y::R), ψ(x)' * H(x, y) * ψ(y))); E
end; E
```

```math
H \mapsto \mathcal{P}\left(ψ \mapsto \int_{x,y}ψ\left(x\right)^{*}\cdot H\left(x, y\right)\cdot ψ\left(y\right)\right)
```

```julia
redux(vdiff(E); settings=symmetry_settings) 
```

```math
H \mapsto ψ \mapsto \mathtt{d} \mapsto 2.0\cdot \left(\int_{y}H\left(\mathtt{d}, y\right)\cdot ψ\left(y\right)\right)
```


## The Least Action Principle

WIP

```julia
_, ctx = @pct begin
    @space X begin
        type = (RF, ) -> RF
        linear = true
    end
end;  
```

```julia
f, _ = @pct _ ctx (L::RO, D::X) -> pullback((r::RF) -> sum((t::R), L(r(t), D(r)(t)))); f
```

```math
\left(L, D\right) \mapsto \mathcal{P}\left(r \mapsto \int_{t}L\left(r\left(t\right), D\left(r\right)\left(t\right)\right)\right)
```

```julia
redux(vdiff(f); settings=custom_settings(:clench_sum=>true))
```

```math
\left(L, D\right) \mapsto r \mapsto \left(D^{T}\left(\mathtt{d} \mapsto \nabla \left(\mathtt{z}_{1} \mapsto L\left(r\left(\mathtt{d}\right), \mathtt{z}_{1}\right)\right)\left(D\left(r\right)\left(\mathtt{d}\right)\right)\right)+\mathtt{d} \mapsto \nabla \left(\mathtt{z}_{2} \mapsto L\left(\mathtt{z}_{2}, D\left(r\right)\left(\mathtt{d}\right)\right)\right)\left(r\left(\mathtt{d}\right)\right)\right)
```

## Pullback of Convolution

```julia
Res, _ = @pct (g::RF, w::RF) -> begin
    let conv = (f::RF) -> (t::R) -> ∑((τ::R), f(τ) * g(t - τ))
        pullback((f::RF) -> ∑((t::R), w(t) * conv(f)(t))
    )
    end
end; Res
```

```math
\begin{aligned}
&\left(g, w\right) \mapsto \mathrm{let}\\
&\quad conv = f \mapsto t \mapsto \int_{τ}f\left(τ\right)\cdot g\left(\left(-1.0\cdot τ+t\right)\right)\\
&\quad \mathcal{P}\left(f \mapsto \int_{t}conv\left(f\right)\left(t\right)\cdot w\left(t\right)\right)\\
&\mathrm{end}
\end{aligned}
```

```julia
vdiff(eval_all(Res))
```

```math
\left(g, w\right) \mapsto f \mapsto \mathtt{d} \mapsto \int_{t}w\left(t\right)\cdot g\left(\left(-1.0\cdot \mathtt{d}+t\right)\right)
```

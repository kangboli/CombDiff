# Tensor Calculus



## Quadratic Form

As a familiar example, we can differentiate $x^{\dagger} A x$, where $A$ is Hermitian

```julia
f, _ = @pct (A::Her) -> pullback((x::CV) -> sum((i, j), x(i)' * A(i, j) * x(j)))
blaserize(f)
```

```math
A \to \mathcal{P}\left(x \to x^{\dagger}\cdot A\cdot x\right)
```

```julia
df = redux(vdiff(f), settings=symmetry_settings()) |> blaserize
```

```math
A \to x \to 2.0 \cdot A\cdot x
```


## Order-3 Tensor Contraction

For a three-way contraction of a third order super-symmetric tensor as a functional
program
```julia
f, ctx = @pct begin
    @space ST begin
        type=(N,N,N) -> R
        symmetries=(((2,1,3), :id), ((1,3,2), :id))
    end

    (T::ST) -> pullback((x::RV) -> sum((i, j, k), T(i, j, k) * x(i) * x(j) * x(k)))
end; f
```

Output:
```math
T \mapsto \mathcal{P}(x \mapsto \Sigma_{i,j,k}x_{i}\cdot x_{j}\cdot x_{k}\cdot T_{i, j, k})
```

You can then differentiate the program to get the gradient, which is just another functional program
```julia
df = redux(vdiff(f); settings=symmetry_settings())
```

Output:
```math
T \mapsto x \mapsto \mathtt{d} \mapsto (\Sigma_{i,k}x_{i}\cdot x_{k}\cdot T_{i, \mathtt{d}, k})\cdot 3.0
```

For those who want the pullback instead
```julia
TODO: make the API for this.
```

Getting you this stage is the main purpose of `CombDiff`. You can compile the DSL
to a correct implementation for reference, but you should implement the gradient yourself 
to best fit with the rest of your codebase and for optimal performance.
```julia
println(MacroTools.striplines(codegen(df)))
```

```julia
(T,)->begin
        (x,)->begin
                let _t = zeros(size(T, 2))
                    for _d = 1:size(T, 2)
                        _t[_d] = let _sum = 0
                                    @inbounds for k = 1:size(x, 1)
                                            _sum += @inbounds(for i = 1:size(x, 1)
                                                        _sum += x[i] * x[k] * T[i, _d, k]
                                                    end)
                                        end
                                    _sum
                                end * 3.0
                    end
                    _t
                end
            end
    end
```

## CANDECOMP/PARAFAC

```julia
f, _ = @pct begin
    @space T3 begin
        type=(N,N,N)->R
    end
    (T::T3) -> pullback((X::RM, Y::RM, Z::RM) -> 
            sum((i,j,k), (T(i,j,k) - sum(n, X(i,n) * Y(j,n) * Z(k,n)))^2))
end; f
```

```math
T \mapsto \mathcal{P}\left(\left(X, Y, Z\right) \mapsto \sum_{i,j,k}\left(\left(-1.0\cdot \left(\sum_{n}X_{i, n}\cdot Z_{k, n}\cdot Y_{j, n}\right)+T_{i, j, k}\right)\right)^{2}\right)
```

```julia
vdiff(f)
```

```math
\begin{aligned}
T \mapsto \left(X, Y, Z\right) \mapsto \left(\mathtt{d}, \mathtt{d}_{1}\right) \mapsto -2.0\cdot \left(\sum_{j,k}Z_{k, \mathtt{d}_{1}}\cdot Y_{j, \mathtt{d}_{1}}\cdot \left(-1.0\cdot \left(\sum_{n}X_{\mathtt{d}, n}\cdot Z_{k, n}\cdot Y_{j, n}\right)+T_{\mathtt{d}, j, k}\right)\right), \\
\left(\mathtt{d}, \mathtt{d}_{1}\right) \mapsto -2.0\cdot \left(\sum_{i,k}X_{i, \mathtt{d}_{1}}\cdot Z_{k, \mathtt{d}_{1}}\cdot \left(-1.0\cdot \left(\sum_{n}X_{i, n}\cdot Z_{k, n}\cdot Y_{\mathtt{d}, n}\right)+T_{i, \mathtt{d}, k}\right)\right),\\
\left(\mathtt{d}, \mathtt{d}_{1}\right) \mapsto -2.0\cdot \left(\sum_{i,j}X_{i, \mathtt{d}_{1}}\cdot Y_{j, \mathtt{d}_{1}}\cdot \left(-1.0\cdot \left(\sum_{n}X_{i, n}\cdot Z_{\mathtt{d}, n}\cdot Y_{j, n}\right)+T_{i, j, \mathtt{d}}\right)\right)
\end{aligned}
```

## Electron Repulsion Integrals

```julia
_, ctx = @pct begin    
    @space T begin
        type = (N,N,N,N) -> C
        symmetries = (((2, 1, 4, 3), :conj), ((3, 4, 1, 2), :id))
    end
end;
```

```julia
f, _ = @pct _ ctx (J::T) -> pullback((C::CM) -> sum((i, j, p, q, r, s),
    C(p, i)' * C(q, i) * C(r, j)' * C(s, j) * J(p, q, r, s)))
```

```math
J \mapsto \mathcal{P}\left(C \mapsto \sum_{i,j,p,q,r,s}J_{p, q, r, s}\cdot C_{s, j}\cdot C_{q, i}\cdot C_{p, i}^{*}\cdot C_{r, j}^{*}\right)
```

```julia
df = redux(vdiff(f); settings=symmetry_settings())
```

```math
J \mapsto C \mapsto \left(\mathtt{d}, \mathtt{d}_{1}\right) \mapsto \left(\sum_{j,q,r,s}J_{\mathtt{d}, q, r, s}\cdot C_{s, j}\cdot C_{q, \mathtt{d}_{1}}\cdot C_{r, j}^{*}\right)\cdot 4.0
```

## Hessian Vector Product

```julia
df |> get_body |> decompose |> pp |> simplify |> first 
```

```math
\left(C, \mathtt{k}\right) \mapsto \left(\mathtt{a}, \mathtt{a}_{1}\right) \mapsto 4.0\cdot \left(\sum_{\mathtt{d},\mathtt{d}_{1},p,s}\mathtt{k}_{\mathtt{d}, \mathtt{d}_{1}}\cdot C_{s, \mathtt{a}_{1}}\cdot J\left(\mathtt{d}, p, s, \mathtt{a}\right)^{*}\cdot C_{p, \mathtt{d}_{1}}^{*}+\sum_{\mathtt{d},\mathtt{d}_{1},p,r}J\left(\mathtt{d}, p, \mathtt{a}, r\right)\cdot C_{p, \mathtt{d}_{1}}\cdot C_{r, \mathtt{a}_{1}}\cdot \mathtt{k}_{\mathtt{d}, \mathtt{d}_{1}}^{*}+\sum_{\mathtt{d},j,r,s}\mathtt{k}_{\mathtt{d}, \mathtt{a}_{1}}\cdot C_{s, j}\cdot J\left(\mathtt{d}, \mathtt{a}, s, r\right)^{*}\cdot C_{r, j}^{*}\right)
```

## Localized Wannier Functions

```julia
_, ctx = @pct begin
    @domain BZ begin
        base = I
        periodic = true
    end
    
    @domain X begin
        symmetric = true
        contractable = false
    end
    
    @space Mmn begin
        type = (N, N, BZ, BZ) -> C
        symmetries = (((2, 1, 4, 3), :conj),)
    end

    @space SV begin
        type = (I,) -> R
        symmetries = (((1,), :ineg),)
    end
    
    @space Gauge begin
        type = (N, N, BZ) -> C
    end
end;
```

```julia
f, _ = @pct _ ctx (S::Mmn, w::SV) -> pullback((U::Gauge) -> 
    begin
        ρ = (n::N, b::X) -> sum((k::BZ, p, q), U(p, n, k)' * S(p, q, k, k + b) * U(q, n, k + b))
        sum((n, b::X), w(b) * ρ(n, b)' * ρ(n, b))
    end); f
```

```math
\begin{aligned}
&\left(S, w\right) \mapsto \mathcal{P}\left(U \mapsto \mathrm{let}\right.\\
&\quad ρ = \left(n, b\right) \mapsto \sum_{k,p,q}U\left(q, n, \left(b+k\right)\right)\cdot S\left(p, q, k, \left(b+k\right)\right)\cdot U\left(p, n, k\right)^{*}\\
&\quad \sum_{n,b}w\left(b\right)\cdot ρ\left(n, b\right)\cdot ρ\left(n, b\right)^{*}\\
&\left.\mathrm{end}\right)
\end{aligned}
```

```julia
df = redux(vdiff(eval_all(f)); settings=symmetry_settings())
```


```math
\left(S, w\right) \mapsto U \mapsto \left(\mathtt{d}, \mathtt{d}_{1}, \mathtt{d}_{2}\right) \mapsto 4.0\cdot \left(\sum_{b,p,k,\mathtt{i},q}w\left(b\right)\cdot U\left(q, \mathtt{d}_{1}, k\right)\cdot U\left(p, \mathtt{d}_{1}, \left(\mathtt{d}_{2}+b\right)\right)\cdot S\left(\mathtt{d}, p, \mathtt{d}_{2}, \left(\mathtt{d}_{2}+b\right)\right)\cdot S\left(\mathtt{i}, q, \left(b+k\right), k\right)\cdot U\left(\mathtt{i}, \mathtt{d}_{1}, \left(b+k\right)\right)^{*}\right)
```

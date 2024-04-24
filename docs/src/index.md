# Introduction

## A first example

`CombDiff` helps you differentiate a functional program written in a DSL. It is
made to tackle challenges in quantum many-body problems, which are full of
tensor calculus with symmetries. As a first example, you can define a three-way
contraction of a third order super-symmetric tensor as a functional program
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
df = redux(vdiff(f); settings=symmetry_settings)
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


## What makes it different

`CombDiff` is a package for combinatory differentiation, which is neither
algorithmic/automatic differentiation (AD) nor symbolic differentiation. It is
not even based on the chain rule. Instead, it is based on the $\mathbf{B}$-rule
and the $\mathbf{C}$-rule, which are rules for differentiating the $\mathbf{B}$
and $\mathbf{C}$ combinators.  These combinators form a complete basis for
functions whereas the composition does not. This enables the *proper*
differentiation of general functions beyond what is possible with composition-based systems.


### Compared to current symbolic differentiation systems 

- `CombDiff` is much more general because anything expressible as a functional
  program, such as the tensor calculus, is within coverage.
- its gradient expression does not scale with the problem because it does not
  differentiate one tensor element at a time. It differentiates variationally.
- you can compile and run it because it is a functional DSL. The performance
  will be reasonable since tensor operations are mapped to BLAS (will use
  tensor contraction engines in the future). 

### Compared to AD 

`CombDiff` gives you a clean gradient
as a mathematician expects. You don't need to 
- build a computational graph that blows up when the problem is large. 
- write a custom pullback that makes you wonder why not just derive the gradient yourself.
- carefully put mutations into an immutable framework to define any new tensor operations. 
- cleverly shoehorn a function into a composition and get a overhead up to $10\times$ in everything.
- indirectly optimize/parallelize the backward pass by tweaking the forward pass.

## State of development

There is enough features implemented for it to be used as an `Einsum` engine
that is symbolically differentiable and gets the symmetry factor right.  You can 
also use it for less sophisticated differentiation.

These language features are implemented and can be differentiated.

- Functions and tensor as closures.
- Delta functions (conditionals).
- `let` clauses.
- Vector spaces as types.
- Basic symbolic arithmetics.
- Contractions.


### What to do about iterations



There is intentionally no `for/while/do` loop in `CombDiff`. They provide
a level of generality that mathematical models don't need at the cost of the
losing the mathematical structures, which we need for producing a clean gradient.
Instead, iterations will be supported in two mechanisms. The first is independent
iterations, which is implemented with closures. For example, a scalar vector
multiplication can be defined as 
```julia
@pct let svm = (a::R, v::RV) -> (i::N) -> a * v(i) ...
```
One should use this to do map-like operations. Reduce-like operations 
should be implemented with a contraction such as
```julia
@pct (v::RV) -> sum((i::N), v(i)' * v(i))
```


The other mechanism is sequential iteration. This is not yet implemented, but the  
theory has been worked out. Two operators will be supported 
- To differentiate through fixed point problems such as the gradient descent
  and mean field theories, use the `argmin`: this maps a function to one of
  its stationary points. One can analytically differentiate through `argmin`
  instead of unrolling the iterations, which will blow up the memory. This is also known as the implicit differentiation.
- For propagation problems such as finite difference time domain and neural
  networks, use the `omega`: this applies a parametrized sequence of functions
  to an input. The pullback of this can be analytically derived. Linear algebra
  algorithms also fall under this category.

## Where it is going

These are features that was planned from the start and will be implemented next.

- Second quantization.
- Implicit differentiation.
- `omega`.



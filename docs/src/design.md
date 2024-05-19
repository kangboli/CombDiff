
## Design notes


### AST nodes as types

Different AST nodes such as an addition or a multiplication are treated as
different Julia types. The original purpose is to leverage multiple dispatch and
abstract types to simulate the _sum type_ used to represent AST nodes in
functional languages instead of having long if statements. In retrospect, this
could have been a mistake because symbolic manipulation of the AST changes its
type, and that causes type instability unless we are using a proper sum type.
Type instability seems to be a performance killer in the long run for a Julia
package, but the alternative is to through types out of the window and save the
type of AST nodes as a field in the `struct`, which might work better but is
damn ugly.

### Domain Boundaries as Implicit Variables

The variables used in the domain boundaries are implicitly declared and
assigned the base type of the domain. This is an ad-hoc treatment that
nevertheless avoids a lot of boilerplates. It can be desirable to treat this more 
properly and reduce the boilerplates with syntax sugars.

### Conflicting simplifications

Generally rewrites that non-uniquely simplify  the expression are problematic
(as opposed to the ones that either do not simplify or are unique). Such rules
include factorization (gcd based) and clench sum, which should be sometimes
disabled depending on the context.

### `make_node`

All nodes are constructed through `make_node(T, terms...)`. We use this instead
of `T(terms...)` so that all nodes share a common constructor. This allows us
to do type inference and e-class reduction within one generic constructor.
The drawback  is the clumsy syntax, so we provide a syntax sugar for each type of node
that calls `make_node` underneath.


### `PCTVector`

We use a `PCTVector` instead of the builtin vector in Julia. This reason is to
make it a `APN` so that we can treat it as a node in the *AST*. This is
impossible if we use Julia's builtin vector or subtype `AbstractVector`.
A second reason is that we plan to use Julia vectors as "Static Vectors" in
our theory so as to do symbolic linear algebra.


## TODO

- Algorithm for reducing the exponential graph.
- Second quantization.
- Better type system and performance optimization (type stability).

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


## Compared to symbolic differentiation 

- `CombDiff` does not differentiate one at a time

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


# PCT

This package is a proof-of-concept implementation of variational
differentiation for quantum chemistry.

## Usage

Coming soonish.



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


# PCT

This package is a proof-of-concept implementation of variational
differentiation for quantum chemistry.

## Usage

Coming soonish.



## Design notes

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


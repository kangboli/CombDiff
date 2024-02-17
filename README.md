# PCT

This package is a proof-of-concept implementation of variational
differentiation for quantum chemistry. The goal is to be able to be able to
express quantum chemistry models including those written in the second
quantization notation and give the derived-by-hand quality gradient by
literally giving the latex formula that is otherwise produced by hand.

This package is not just another symbolic algebra system or automatic
differentiation system. It is a language that is simultaneously capable of
both.


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


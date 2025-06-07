# A Tour of `CombDiff`

## Running `CombDiff`

### A `CombDiff` Program

A `CombDiff` program is defined with the `@main` macros. The program takes no
input by default and returns a value as the output. For example,
```julia
f, _ = @main begin
    x = 1
    y = 2
    x + y
end
```
To run this program, first transpile it to Julia with `codegen`.
```julia
codegen(f)

# :(()->begin
#           let x = 1, y = 2
#               x + y
#           end
#       end)
```
We can evaluate this code with `eval` and call it with no argument 
```julia
eval(codegen(f))()
# 3
```

### Type Context and Environment

For the program to take inputs, one can access Julia variables in the scope where
the program is defined. For example,

```julia
x = 4
f, args = @main 2x
f 
# (x) -> 2 * x
args
# 1-element Vector{Int64}:
#  3
```
One can then run the program with `x = 3` 
```julia
eval(codegen(f))(args...)
# 6
```

To write a library, which includes the definitions of types and global functions,
one can use the `@comb` macro
```julia
f, ctx = @comb begin
    struct Point
        x::R
        y::R
        z::R
    end

    get_x = (p::Point) -> p.x
end

ctx[:Point]

# Point(x::R * y::R * z::R)

f
# let
#     get_x = (p) -> p.x
#     _
# end
```
The `ctx` variables holds the type context, which is all the types that has
been defined so far. The `f` variable does the same for variables.
To make use of the context, one can pass them into `@main`

```julia
g, _ = @main get_x(Point(1.0,2.0,3.0)) f ctx

g
# () -> let
#     get_x = (p) -> p.x
#     get_x(Point(1.0, 2.0, 3.0))
# end
```
This simply places the main program into the context. The `@main` macro also
initiate a type inference, and an error will be thrown if a variable or type
cannot be resolved from the context.
```julia
@main get_y(Point(1.0,2.0,3.0)) f ctx
# ERROR: UndefVarError: `get_y` not defined
# ...
```
Since `get_y` is not in the variable context `f`, `CombDiff` looks for it in
Julia's scope, where it is not defined either. We can now compile and run
`g` as before
```julia
eval(codegen(g))()
# 1
```



### Oneliner Mode

Instead of writing, compiling, and invoking a program, one can do all three in one 
macro `@mein` which stands for mein einsum. 
```julia
x = 4
@mein x + 2
# 6
```
As the name suggests, this can be used as an einsum frontend. 
Do not worry about the syntax for now. We will introduce them later.
```julia
M = 4
A = ones(M, M)
@mein sum((i::N{M})->A(i, i))
# 4
```
The type `N{M}` denotes natural numbers up to `M`. We have used dependent types
because `M` is a variable that parameterizes the type `N`. 

Since `CombDiff` is a language, we can do more general things than einsum.
For example, Fourier transform every row of `A`.
```julia
using FFTW
@mein (i::N{M}) -> FFTW.fft((j::N{M}) -> A(i, j))
# 4-element Vector{Vector{ComplexF64}}:
#  [4.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im]
#  [4.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im]
#  [4.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im]
#  [4.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im, 0.0 + 0.0im]
```
Notice that `FFTW` is an external module that is passed to the `CombDiff`
program as an input.



## Differentiation

To target a function for differentiation, put `grad` around the it.
```julia
f, _ = @main grad((x::R) -> 2x)
# () -> grad((x) -> 2 * x)
```
The differentiation can be done with 
```julia
eval_pullback(f)
# () -> (x) -> 2
```

As the name `eval_pullback` suggests, `CombDiff` operates in reverse modes with
pullbacks, which one can directly obtain
```julia
f, _ = @main pullback((x::R) -> 2x)
eval_pullback(f)
# () -> (x, _k) -> 2 * _k
```
A variable prefixed by an underscore such as `_k` is compiler generated. The
raw pullback is useful for Hessian vector products and authoring reverse rules
for AD systems. The gradient is just the pullback with `_k` set to `1`, so the
two are equally supported. 

Of course, the differentiation is not limited to $x \mapsto 2x$. We will see
more advanced examples including backpropagation, tensor algebra, and ode
solves. As a first taste, lets consider differentiating the trace.
```julia
f, _ = @main grad({M}(A::RM{M, M}) -> sum((i::N{M}) -> A(i, i)))
d_f = eval_pullback(f)
# () -> {M}(A) -> (_a, _a_1) -> delta(_a, _a_1, 1)

eval(codegen(d_f))()(3 .* ones(3,3))
# 3×3 Matrix{Float64}:
#  1.0  0.0  0.0
#  0.0  1.0  0.0
#  0.0  0.0  1.0
```
The trace function we defined is parametrized by `M`, which is the dimension of
the input matrix `A`. The dependent type `RM{M, M}` can type-check that `A`
must be square. The output is the identity matrix as expected.

```julia
f, _ = @main grad((A::R, B::R) -> A % B)
eval_pullback(f)
```

## Functions & Tensors

### Functions

`CombDiff` only support anonymous functions. To give a name to a function,
write `name = (x::R) -> ...`. To have multiple assignments in a function, write a `begin ... end` block. For example,
```julia
f, ctx = @comb begin
    my_func = (q::R, p::R) -> begin
        q = q + 2
        q^4
    end
end
```
`CombDiff` does not provide a way to specify a return type. This is because
`CombDiff` is statically typed and enforces strict type stability, so the return type can always be type-inferenced.


One can obtain the gradient similar to before. However, because we have to find
the implementation of `my_func` before differentiating it, the differentiation
is multi-staged. This requires `eval_pullback_full`.
```julia
g, _ = @main grad(my_func) f ctx

eval_pullback_full(g)

# let
#     my_func = (q, p) -> let
#         q = (2+q)
#         (q)^(4)
#     end
#     _pullback_my_func = (q, p, _k) -> let
#         _y = (2+q)
#         _y_1 = (_y)^(4)
#         _l = _k * (_y)^(3) * 4
#         tuple(_l, 0)
#     end
#     () -> (_i, _i_1) -> _pullback_my_func(_i, _i_1, 1)
# end
```

### Closures

We can define functions that capture variables from an outer scope.
```julia
f, _ = @main begin
    x = 4
    (y::R) -> y + x
end
eval(codegen(f))()(5)
# 9
```

Closures can be differentiated either by itself or as an output.
For example, to differentiate a closure, just put `grad` around it.
```julia
f, _ = @main begin
    x = 4
    grad((y::R) -> y + x)
end

eval_pullback(f)

# eval_pullback(f)
# () -> let
#     x = 4
#     (y) -> 1
# end
```

We can also differentiate a function that returns a closure, although 
the differentiation has to be a `pullback` and not `grad`.
```julia
f, _  = @main pullback((x::R) -> (y::R) -> y + x)
eval_pullback(f)

# () -> (x, _k) -> sum((y) -> _k(y))
```
Notice that our sum here is polymorphic. Since the type of `y` is `R` (real numbers), the `sum` is to be interpreted as an integral.


### Call by Value

Our runtime reduction strategy is CBV. For example,
```julia
@mein begin
    mul = (x::R, y::R) -> x * y
    mul(1.0+1.0, 2.0+2.0)
end

# 8.0
```
This code does what most languages would do: it computes $1+1=2$ and $2+2=4$ and
then $2 * 4 = 8$. In terms of reduction strategy, it is the same as
```julia
@mein begin
    x = 1.0 + 1.0
    y = 2.0 + 2.0
    x * y
end

# 8.0
```

### Call by Name

By constrast, our compile time reduction strategy closer to CBN. A function call is
evaluated at compile time if it is a immediately invoked function expressions
(IIFE). For example,
```julia
f, _ = @main ((x::R, y::R) -> x * y)(1.0 + 1.0, 2.0+2.0)
eval_all(f) 

# () -> 8.0
```
Note that $1.0 + 1.0$ can be evaluated either at runtime or compile time, but
$x$ and $y$ are substituted only in an IIFE or symbolic definition, which is as follows.

The walrus operator `:=` is used to make symbolic assignments. The reduction
strategy is basically symbolically substituting all occurrence of a variable
with its RHS. For example, the following code does the same thing as the IIFE.
```julia
f, _ = @main begin
    x := 1.0 + 1.0
    y := 2.0 + 2.0
    x * y
end
eval_all(f) 

# () -> 8.0
```

This mechanism generalizes to functions, which can also be symbolically assigned.
```julia
f, _ = @main begin
    mul := (x::R, y::R) -> x * y
    mul(1.0+1.0, 2.0+2.0)
end
eval_all(f) 

# () -> 8.0
```

The conventional attraction CBN is avoiding infinite loops, but that is
irrelevant for numerical computing. Nevertheless, CBN has two important use
cases in scientific computing context.

1. symbolic tensor computation.
2. trade compute for memory.

### Call by Indexing

There is no tensor type or library in `CombDiff`. 
Instead, **tensors are an evaluation strategy: call by indexing (CBI)**.

In CBI, before calling a function, one first enumerate all input-output pairs
and place them in a tensor. The function calls are then performed through
indexing. For example, to create a matrix of ones, we can write
```julia
M = 2
@mein (i::N{M}, j::N{M}) -> 1

# 2×2 Matrix{Int64}:
#  1  1
#  1  1
```
This code serves the same purpose as `ones(M, M)`. However, importantly, the
tenser is expressed without a library routine or a tensor type definition.
Evidently, we cannot use CBI everywhere because a function can have infinite
number of possibilities for its inputs. The question is then when to use CBI.
The answer is when all input types are of the form `N`, `I{A, B}`, or product
types thereof. To define functions whose inputs are integers, use `I` and
product types thereof.



One can then build slightly more sophisticated examples, where we compute the
inner product between two vectors.
```julia
M = 10
f, args = @main :(begin
    vip = {T}(x::RV{T}, y::RV{T}) -> sum((i::N{T}) -> x(i) * y(i))

    x = (i::N{M}) -> 1
    y = (i::N{M}) -> 2 * x(i)
    vip(x, y)
end)

eval(codegen(f))(args...)

# 20
```
We have again used dependent types to check that `x` and `y` are of the same
length at compile time.


We can differentiate with respect to `y` and get a partial derivative
```julia
M = 10
f, args = @main :(begin
    vip = {T}(x::RV{T}, y::RV{T}) -> sum((i::N{T}) -> x(i) * y(i))

    x = (i::N{M}) -> 1.0
    grad((y::RV{M}) -> vip(x, y))
end)

d_f = eval_pullback_full(f)

# (M) -> let
#     vip = {T}(x, y) -> sum((i) -> x(i) * y(i))
#     _pullback_vip = {T}(x, y, _k) -> tuple((_a) -> _k * y(_a), (_a) -> _k * x(_a))
#     x = (i) -> 1.0
#     (y) -> _pullback_vip(x, y, 1)(2)
# end
```
We can in fact check the our result is correct with symbolic tensor algebra
```julia
eval_all(CombDiff.strip_copy(d_f))

# (M) -> (y) -> (_a) -> 1.0
```


## Expressions  & QFT

### Tuple & Splatting

!!! warning "not differentiable"

    Differentiation for splatting is not yet supported.


A function may return a tuple. The tuple can be passed to a next function an splatted.
```julia
f, _ = @main begin 
    my_func_1 = (x::R) -> (x, x + 1)
    my_func_2 = (x::R, y::R) -> x * y

    my_func_2(my_func_1(3)...)
end

eval_all(CombDiff.strip_copy(f))

# output

() -> 12
```

One can also assign a tuple to a variable and unpack it later
```julia
f, _ = @main begin 
    x = 3
    l = (x, x + 1)
    my_func_2 = (x::R, y::R) -> x * y
    my_func_2(l...)
end

eval_all(CombDiff.strip_copy(f))

# output

() -> 12
```


### Conditionals

There is no Boolean (like C) or `if then else` in `CombDiff`. Equality testing
is done by `delta`, whereas inequality testing is done by `indicator`. For
example, a checkerboard mask can be constructed as
```julia
@mein (i::N{4}, j::N{4}) -> delta((i + j) % 2, 1, 1)

# 4×4 Matrix{Int64}:
#  0  1  0  1
#  1  0  1  0
#  0  1  0  1
#  1  0  1  0
```

Such as mask can be applied to a matrix to extract selected elements. 
The pullback of this operation is applying the same mask to `_k`.
```julia
f, _ = @main pullback({M}(x::RM{M, M}) -> (i::N{M}, j::N{M}) -> delta((i + j) % 2, 1, x(i, j)))
eval_pullback(f)

# (%) -> {M}(x) -> (_a, _a_1) -> delta(1, %((_a+_a_1), 2), _k(_a, _a_1))
```
Currently, `CombDiff` does not support differentiating the equality test itself
such as `grad((x) -> delta(x, y, k))`, but this will come soon.


For inequality testing, we use the indicator function. For example, constructing a submatrix looks like
```julia
@mein (i::N{4}, j::N{4}) -> indicator(i, 2, indicator(j, 2, 1))

# 4×4 Matrix{Int64}:
#  1  1  0  0
#  1  1  0  0
#  0  0  0  0
#  0  0  0  0
```
It is worth noting that the indicator function is not really a primitive, but a combination of contraction and delta.
```julia
f, _ = @main (j::N{4}) -> sum(i::N{2} -> delta(i, j, 1)) 
first(simplify(f))

# () -> (j) -> indicator(j, 2, 1)
```

This restricted form of conditionals allows "propagation of tests". For example,
```julia
f, _ = @main begin 
    my_func = (x::R) -> x + 666.0
    (i::N{4}, j::N{4}) -> begin
        x = delta(i, j, 2.0)
        y = 2 * x
        z = pullback(my_func)(2, y)
        z
    end
end

first(simplify(f))

# let
#     my_func = (x) -> (666.0+x)
#     x = 2.0
#     y = x * 2
#     z = P(my_func)(2, y)
#     () -> (i, j) -> delta(j, i, z)
# end
```
This is rather important for optimizing generated code.


### Second Quantized Field


`CombDiff` supports second quantized field. All fields are fermionic
for now. Support for Bosons and other fields will come when needed.
To use second quantization, write `:` followed by some name such as
`a`. This field can be evaluated at some site/point `i`. To apply 
the Wick theorem, surround your second quantization with `vac_exp`

```julia
f, _ = @main (i::N, j::N) -> vac_exp(:a(i) & :a(j)')
first(simplify(f))

# () -> (i, j) -> delta(j, i, 1)
```

Can can define a Hamiltonian and then evaluate an expectation value
```julia
f, _ = @main {M}(h::RM{M, M}) -> begin
    sum((i::N{M}, j::N{M}) -> h(i, j) * vac_exp(:a(i) & :a(j)'))
end
first(simplify(f))

# () -> {M}(h) -> sum((j) -> h(j, j))
```

To write a sequential program with second quantization, one must write in CBN
to avoid evaluating the creation/annihilation operators as exponential large
matrices. Support for matricizing the field operators will be added via CBV.
```julia
N_b = 10
N_o = 4

f, _ = @main begin
    (h::RM{N_b, N_b}) -> begin
        H := sum((i::N{N_o}, j::N{N_o}) -> :II(h(i, j)) & :a(i) & :a(j)')
        vac_exp(H)
    end
end

simplify(f)

# () -> {M}(h) -> sum((j) -> h(j, j))
```


## Types & Symmetries

### Basic Type

Because `CombDiff` is a DSL for numerical computing within Julia, the built in types 
are limited to numbers 

- `N`: natural numbers. Mostly used for indices.
- `Z` or `I`: integers.
- `R`: double precision real numbers. Reduced precision may be implemented if needed.
- `C`: double precision complex numbers.

There is no boolean or string, which are not essential for numerical computing
and complicates differentiation. 


### Dependent Type

Dependent types are parametric types whose parameters are runtime value. In
`CombDiff`, dependent types are used to describe the size of tensors. This
enables the compile time symbolic computation of the size of every tensor via
type inference.

### Domain


A `Domain` describes an interval on a base type such as `N`, where the interval can be parametrized
For example, an interval $[1, T]$ can be declared as
```julia
f, ctx = @comb begin
    @domain M{T} begin
        base=N
        lower=1
        upper=T
    end
end

ctx[:M]

# {T} ->> N:[1, T]
```

The type can be used for many compiler tricks such as  eliminating dead
branches. 
```julia
g, _ = @main {T::N}(x::M{T}) -> indicator(T+1, x, 1) f ctx

first(simplify(g))

# () -> {T}(x) -> 0
```


### Spaces

Spaces declare vectors spaces or types of functions, which have domains and
codomains. A function type can also be parametrized.
```julia
f, ctx = @comb begin
    @space T3{M} begin
        type=(N{M}, N{M}, N{M}) -> R
    end
end
```

These types are respected throughout differentiation
```julia
M = 5
g, _ = @main (b::T3{M}) -> grad((x::RV{M}) -> sum((i,j,k) -> b(i, j, k) * x(i) * x(j) * x(k))) f ctx

eval_pullback(g)

# (M) -> (b) -> (x) -> (_a) -> (sum((j, k) -> x(j) * x(k) * b(_a, j, k))+sum((i, k) -> x(i) * x(k) * b(i, _a, k))+sum((i, j) -> x(i) * x(j) * b(i, j, _a)))
```

### Symmetries

Tensors or functions have symmetries, which can be encoded in `@space` and
reasoned by the compiler. The symmetries are encoded as maps on the tensor that
leaves it invariant. 
```julia
f, ctx = @comb begin
    @space T3{M} begin
        type=(N{M}, N{M}, N{M}) -> R
        symmetries=(
            f->(i,j,k)->f(j,i,k),
            f->(i,j,k)->f(i,k,j),
        )
    end
end
```

These symmetries can be used to do post-differential compiler optimization
```julia
g, _ = @main (b::T3{M}) -> grad((x::RV{M}) -> sum((i,j,k) -> b(i, j, k) * x(i) * x(j) * x(k))) f ctx

eval_pullback(g) |> fast_symmetry_reduction

# (M) -> (b) -> (x) -> (_a) -> sum((j, k) -> x(j) * x(k) * b(j, k, _a)) * 3.0
```

### Product Type

!!! warning "WIP" 

    This is barely tested.


A product type can be defined with `struct`.
```julia
f, ctx = @comb begin
    struct GridPoint
        x::N
        y::N
        z::N
    end
end
```

It behaves similar to a Julia `struct` in that a constructor is provided 
and its fields can be accessed with `.`
```julia
g, _ = @main ((r::GridPoint) -> r.x)(GridPoint(1, 2, 3)) f ctx

eval(codegen(eval_all(g)))()
1
```

Most importantly, yes, you can differentiate it
```julia
g, _ = @main grad((r::GridPoint) -> r.x) f ctx
eval_pullback(g)

# () -> (r) -> (GridPoint)(1, 0, 0)
```

### Zero Cost Meshgrid

Grid points are nuanced because they are vectors and indices at the same time.
Treating it as vectors causes slow indexing. Treating it as indices loses the
vector algebra. Converting back and forth causes excessive code complexity.
This problem cannot be resolved at the library level, but the compiler 
can resolve this as a zero cost abstraction.
```julia
g, _ = @main begin
    psi = (r::GridPoint) -> r.x + r.y + r.z 
    sum((r::GridPoint) -> psi(r))
end f ctx

to_cbi(g) |> first |> verbose |> println
# let
#     psi = cbi((r) -> (((GridPoint(x::N * y::N * z::N))(r))(1)+((GridPoint(x::N * y::N * z::N))(r))(2)+((GridPoint(x::N * y::N * z::N))(r))(3)))
#     () -> sum((r) -> get_data(psi)(r))
# end
```
In the output, the `r` are of the type natural numbers, so there is only plain
tensor algebra happening. The `cbi` and `get_data` wraps and unwraps the tensor
so that `psi` still takes a `Point`  as the input. This abstraction can be
combined with our second quantization to make it easy to study 2D/3D lattice
models.


## Sequential Iteration

### For loop

As a functional programming language, `CombDiff` does not provide recursion,
which is not a good idea for iteration in scientific computing contexts.
Instead, it emulates the for loop with `seq`, which applies 
a sequence of function parametrized by an integer. For example, multiplying 
`1` with `a` for `10` times takes the form
```julia
f, _ = @main (a::R) -> seq((i::N{10}) -> 
                           (x::R) -> a * x)(1)
```

This should be considered similar to 
```julia
tmp = 1
for i in 1:10
    tmp = (x) -> (a * x)(tmp)
end
tmp
```

One can differentiate this and yield an adjoint method
```julia
f, _ = @main grad((a::R) -> seq((i::N{10}) -> (x::R) -> a * x)(1))
eval_pullback_full(f)

# () -> (a) -> let
#     _y = (_T) -> seq((_t) -> (x) -> x * a)(1)
#     _l = (_M) -> seq((_m) -> (_k_1) -> _k_1 * a)(1)
#     sum((i) -> _l((10+(-1) * i)) * _y(((-1)+i)))
# end
```
The output requires a few more compiler optimization tricks that 
are yet to be implemented.

### Fixed point & Argmax

!!! note "Coming soon"

## Memory Model

### Semi-static Memory



### Side-effect $\Leftrightarrow$ purity

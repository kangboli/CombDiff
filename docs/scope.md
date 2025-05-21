# Tensor Expressions
    
Unlike Fortran/MATLAB/Julia/Numpy, which construct and transform tensors with
mutating statement, `CombDiff` does so with expressions, which is similar to `einsum`.

## Initializing Tensors

Similar to how `x = 1` assigns the value `1` to variable `x`, we can assign a tensor to a variable
```julia
x = (i::N{M}) -> 1
```
This code does the same thing as `x = ones(M)` without a library function.

As a less trivial example, we can construct a Vandermonde matrix with
```julia
v = (i::N{M}, j::N{M}) -> x(i)^(j-1).
```

## Transforming Tensors

Broadcasting should not involve any guess work. To add a vector to every column of a matrix, we write
```julia
B = (i::N, j::N) -> A(i, j) + v(i)
```


You can use tensor expressions as a fancy einsum
```julia
C = (i::N, j::N) -> ∑(k::N{10}, A(i, k) * B(k, j) + C(i, j))
```

Unlike data, expressions can be inlined. To apply `fft` on each column of a matrix, we write
```julia
u = (g::N) -> fft((i::N) -> v(g, i))
```

Tensors can be nested. To permute a matrix, we write
```julia
u = (i::N, j::N) -> v(σ(i, j)...)
```

# Stable Dependent Type 

`CombDiff` implements a dependent type system to keep track of the dimension of
tensors. For example `::RV{N_e}` is a real vector of `N_e` dimensions. Further
more, we impose type stability, which means that the return type of a function
can be inferred from the type of its input. Combined with dependent types, this
means that we restrict ourselves to stable dimension. For example, `sum` is
stable but `filter` is not.

Knowing the dimension of every tensor symbolically at compile time affords us a
few important future benefits

- Dimension mismatch can be caught at compile time.
- Automatic memory allocation and reuse (inplacing). 
- Avoid branch divergence (GPUs do not like that).

The price to pay is that 
- no dimension unstable functions such as `filter` and `drop`.  
- no general recursion. 


# Dimensions

## Accessing Dimensions

There is no direct way to access the dimension of a tensor like `size(A, 2)`.
Instead, declare the dimensions as a type parameter and constrain the tensor to
have the right dimension. For example, to take the trace of a square matrix 

```julia
tr = {N}(A::RM{N, N}) -> sum(i, A(i, i))
```

As another example, let's find the last element of a vector 
```julia
last = {M}(v::RV{M}) -> v(M)
```


## Specifying Dimensions

Since the dimension is a dependent type, one can specify the dimension with a regular variable
```julia
(M::N) -> begin
    tr = (A::RM{M, M}) -> sum(i, A(i, i))
end
```
This version of `tr` only type checks for $M \times M$ matrices.

## Dimension Extraction

If one omits the dimension of an index, it will be extracted from its usage. For example,
```julia
u = (i::N) -> 2 * v(i)
```
The range of `i` will be extracted to be the dimension of `v`. The dimension
cannot always be meaningfully extracted. For example, `(i::N) -> 1` will result
in an error.

# Procedures

## Statement

All statements are `let` as in a functional program with the rest of the scope as its body.
```julia
x = 1
y = 2
x + y
```
This really is 
```juli
let x = 1
    let y = 2
        x + y
    end
end
```

## Inline

A variable will be inlined if it is assigned with `:=`. This can be used to trade compute for memory.
```julia
begin
    x := (i::N{M}) -> 1
    (i::N) -> 2 * x(i)
end
```
This will be inlined as 
```julia
(i::N) -> 2 * 1
```

# Conditional

## Equality Test

Conditional in `CombDiff` is supported with Kronecker Delta.
```julia
delta(i, j, k)
```
This corresponds to the julia code
```julia
i == j ? k : 0
```
This allows for a crucial algebraic manipulation $\sum_i \delta_{i, j}
f(i) = f(j)$. The price to pay is that the two branches must return the
same type.

## Inequality Test

For inequality comparison, we use the indicator function
```julia
I(i, j, k)
```
This corresponds to 
```julia
i <= j ? k : 0
```
Note that the indicator function is not a primitive. It is built from $\delta$
and $\sum$ as $\sum_{p=-\infty}^{j} \delta(i, p, k)$. $\delta$ is a primitive 
and $\sum$ is a special case of $\Lambda$.

These two tests are in principle complete.

# Iteration

## Unordered

<!-- 1. Tensors are congruent with functions
2. Unordered iterations map tensor to tensors.
3. Mapping from functions to functions is a transform (such as Fourier
transform)
4. Unordered iterations are written as transforms. -->

Doubling every entry in a tensor $t$ 
is done by assigning a new function (tensor) to $t$.
```julia
t = (i::N) -> 2 * t(i)
```

## Ordered Stable

To apply $M$ functions of the same family sequentially to an input, we use the
applicator
```julia
result = Λ(i::N{M} -> f(i))(x)
```
This corresponds to 
```julia
result = x
for i in 1:M
    result = f(i)(result)
end
```
This is just expressive enough for scientific problems such as solving an ODE,
which does not need `break` or `continue`. 

Note that `sum` is a special case of `Λ` with 
```julia
sum = (y) -> Λ(i::N{M} -> t::C -> t + y(i))(0).
```

## Fixed Point

To apply the same function to a state until it no longer varies.
```julia
end_state = fixed_point(f, start_state, eps)
```
This corresponds to 
```julia
curr_state = start_state
diff = Inf
while diff > eps
    next_state = f(curr_state)
    diff = norm(next_state - curr_state)
    curr_state = next_state
end
```
These three iteration mechanism should suffice for numerical applications. 



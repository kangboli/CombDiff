# Memory Management & Mutations

`CombDiff` employs a semi-static memory (SSM) model.  To put it into
perspective, lets compare it with static and dynamic memory.

- Static memory:  array size is known numerically at compile time. The compiler can allocate memory by moving the stack pointer.
- Dynamic memory: array size is known numerically at run time. Memory has to be requested from the heap during runtime.
- Semi-static: array size is known symbolically at compile time. Heap memory is still needed, but the syscalls are compiler generated.

A semi-static model is possible only because `CombDiff` is statically typed
with dependent types. This implies that the size of every object is
symbolically known from type inference, enabling the compiler to reuse memory
without buffer overflow. Moreover, since `CombDiff` is a pure language,
variable lifetime is exactly known for timely recycling of its memory.

# Mutable Arguments

`CombDiff` is pure, so function parameters are generally immutable. However,
the caller of a function may know that the arguments it passes in will not be
read again, so the compiler can replace it with a mutating version of the same
function. For example, 
```julia
@main begin
    A = (i::N{M}, N{M}) -> 1
    double(A)
end
```
The caller of `double` created `A`, which is of the type `RM{M}`.  Since we know that 
`A` is never going to be read again, the compiler can optimize the code to be
```julia
@main begin
    A = (i::N{M}, N{M}) -> 1
    double!(mut(A))
end
```
The mutable argument `mut(A)` is of type `RM!(M)`, which is the input type of `double!`.
The `double!` function should have the same output as `double`, but it is allowed to 
reuse the memory of `A`.


# Mutable Parameters

The `double` function looks like the following
```julia
@main double = (A::RM{M}) -> begin
    B = (i::N{M}, j::N{M}) -> 2A(i, j)
    B  
end
```

Due to dependent type and purity, we know that 
- `A` on the rhs will not longer be read in this scope.
- the exclamation mark in `RM!` tells us that the parent scopes will not read `A`.
- both `A` and `B` are `M` by `M` matrices.

This allows us to optimize `double!` to be 
```julia
@main double! = (A::RM!{M}) -> begin
    _ = (i::N{M}, j::N{M}) -> mutate(A(i, j), 2A(i, j))
    B := A
    B  
end
```
This code sets the memory of `A` to `2A`, which is a side effect that returns
no value (`_`). We then alias `B` to `A` and return it. 

# Same Name Partial Mutation

Some times there are more than one piece of memory available for reuse. For example,
To set the first column of `A` to some target `B`, we can write
```
A = (i, j) -> A(i, j) + delta(j, 1, B(i) - A(i, j)) 
```
If both `A` (rhs) and `B` are available for reuse, we will use `A` instead of
`B`. This is a good idea here because we only need to mutate a single column of
`A`. 


## Find Update

When the same name appears on both sides, we symbolically take a difference to
find the update, which is a sparse matrix with only a single nonzero column.
```julia
(i, j) -> delta(j, 1, B(i) - A(i, j))
```

## Optimize Update

This can be optimized using equality graphs and dependent types
```julia
(i, j::N{1}) -> B(i) - A(i, j)
```
The parameters of this function clearly shows which part of the matrix is to be
updated.

## Generate Mutation

We can symbolically compute the updated value at `(i, j::N{1})` by adding `A(i, j)` to it
```julia
(i, j::N{1}) -> B(i)
```

The compiler can then generate the mutations
```julia
_ = (i, j::N{1}) -> mutate(A(i, j), B(i))
```
Effectively, we have implemented `A(:, j) = B` **with pure code**, which is
optimized to a mutation if confluent.  The purity code can be differentiated
into pure code for the gradient, which can also be optimized into mutations.
This theory should generalize straightforwardly to any array mutation.

# Sequential Iteration

The mutation mechanism is necessary to implemented sequential iteration
in `CombDiff` without excessive memory overhead.
Consider the Julia code
```julia
powers = zeros(10)
init = 1
for i in 1:10
    powers[i] = 2 * (i == 1 ? init : power[i - 1])
end
```
This code relies on mutating an element of `powers`  at every iteration. There
are two ways to make this code pure. One is to append one power at a time, which would 
be the approach of a typical functional programming language
```julia
compute_powers(init, n) = if n == 0 
    [init]
else
    let prev = compute_powers(init, n-1)
        [prev..., 2 * prev]
    end
end

compute_powers(1, 10)
```
This approach would not work for `CombDiff` because it does not have stable
dimensions. The compiler is not able to figure out the output dimension of
`compute_powers` using (reasonable) type inference. Moreover, both the memory
and speed of this is completely unacceptable even with tail call optimization
because a `malloc` is called at every iteration.


The `CombDiff` version  would be
```julia
@main {M}(power_init::RV{M}) ->
    seq((i::N{M}) -> (powers::RV{M}) -> begin
        prev = delta(i, 1, init) + delta_not(i, 1, power(i - 1))
        powers = (j::N{M}) -> powers(j) + delta(i, j, 2 * prev - powers(j))
        powers
    end)(power_init)((i::N{10}) -> 0)
```
The compiler can safely optimize this to use mutations
```julia

@main {M}(power_init::RV!{M}) ->
    seq((i::N{M}) -> (powers::RV!{M}) -> begin
        prev = delta(i, 1, init) + delta_not(i, 1, power(i - 1))
        _ = (j::N{i,i+1}) -> mutate(powers(j), 2 * prev)
        powers
    end)(power_init)(mut((i::N{10}) -> 0))
```





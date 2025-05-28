# Evaluation Schemes for Tensors


## Evaluation Schemes

Two common reduction strategies include call by value (CBV) and call by name
(CBN). We need to do a mix of both and a bit more. 

### Call by value

Our runtime reduction strategy is CBV. For example,
```julia
@mein begin
    mul = (x::R, y::R) -> x * y
    mul(1.0+1.0, 2.0+2.0)
end
```
This code does what most langauge would do: it computes $1+1=2$ and $2+2=4$ and
then $2 * 4 = 8$. In terms of reduction strategy, it is the same as
```julia
@mein begin
    x = 1.0 + 1.0
    y = 2.0 + 2.0
    x * y
end
```

### Call by name

By constrast, our compile time reduction strategy closer to CBN. A function call is
evaluated at compile time if it is a immediately invoked function expressions
(IIFE). For example,
```julia
f, _ = @main ((x::R, y::R) -> x * y)(1.0 + 1.0, 2.0+2.0)
eval_all(f) # () -> 8.0
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
eval_all(f) # () -> 8.0
```

This mechanism generalizes to functions, which can also be symbolically assigned.
```julia
f, _ = @main begin
    mul := (x::R, y::R) -> x * y
    mul(1.0+1.0, 2.0+2.0)
end
eval_all(f) # () -> 8.0
```

The conventional attraction CBN is avoiding infinite loops, but that is
irrelevant for numerical computing. Nevertheless, CBN has two important use
cases in scientific computing context.

1. symbolic tensor computation.
2. trade compute for memory.
 
### Call by indexing

To support our tensor expressions, we need a third reduction strategy, which is
call by indexing (CBI).  In this strategy, before calling a function, one first
enumerate all input-output pairs and place them in a tensor. The function calls 
are then performed through indexing.

```julia
M = 10
@mein :(begin
    x = (i::N{M}) -> 1
    y = (i::N{M}) -> 2 * x(i)
    sum(i, x(i) * y(i))
end)
# 20
```

The function `(i::N{M}) -> 1` is functionally the same as `ones(M)`. However,
instead of using a built in function, we achieve the same thing with CBI.

The obvious problem with CBI is that a function can have infinite number of
possibilities for its inputs, so CBI is only to be used as an alternative
semantics for tensor algebra instead of generic function evaluation.
Practically, Whether CBI is used depends on the input type of the function. If
the input types are all one of `N`, `I{A, B}`, or product types thereof, then
the CBI will be used. 

Unlike a tensor library, CBI is a language-level solution to tensor algebra.
This enables compiler optimization and symbolic math for faster tensor algebra.
```julia
M = 10
f, _ = @main :(begin
    x := (i::N{M}) -> 1
    y := (i::N{M}) -> 2 * x(i)
    sum((i::N{M}), x(i) * y(i))
end)

first(simplify(eval_all(f)))
# (M) -> 2 * M
```


## Confluence

All three evaluation strategies should be confluent if there is no infinite
loop.



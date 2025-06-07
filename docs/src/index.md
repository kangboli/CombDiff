## What is `CombDiff` about

### It is a Language

- ✓  It is an experimental domain specific functional programming language.
- ✓  It *describes and compiles* tensor algebra and second quantization.
- × It is not a numerical library for linear/nonlinear/multi-linear algebra.
- × It is not a coupled cluster code generator.
- × It is not a quantum chemistry code/distribution/library/framework.
 
### $O(1)$ Gradient

- ✓  It differentiates *before any evaluation*, thus avoiding the computation graph or expression swell.
- ✓  It produces an gradient abstract syntax tree (AST) resembling hand-written gradient. Examples include tensor algebra, neural networks, ODE solve, structural/functional programming.
- ✓  It is based on Schröfinkel's combinatory logic.
- × It is not based on the chain rule. 
- × It is neither algorithmic nor symbolic differentiation, which evaluate numerically or symbolically before differentiation.
- × It is not based on high-level primitives. There is no matrix/tensor routines at all in the language.


### Compiler Optimization

- ✓ `CombDiff` has a static and dependent type system with type inference. 
- ✓  Tensor sizes and symmetries are encoded in dependent types and propagated through type inference.
- ✓  It  tracks contextual assumptions necessary for compiler optimization.
- × It is not about optimizing single primitives such as finding the optimal contraction order.
- × It is not a symbolic algebra system.

### Target Applications

- ✓  Computational quantum Chemistry & condense matter.
- ?  Quantum computing.
- ?  Machine learning & data science.

### Abstraction

- × `CombDiff` is not meant to be high level.
- ✓ It has a static and dependent type system. Tensor sizes are type parameters.
- ✓ Memory usage is fully inferenced at compile time, so the memory is basically static.



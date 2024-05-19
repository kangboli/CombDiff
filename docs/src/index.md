
`CombDiff` implements the *theory of combinatory differentiation*, which is not
based on the chain-rule or the computation graph. It is based on the
combinatory logic and a set of rules for differentiating the combinators.

Most things are still under development and need more engineering, but the
package is already viable some hard automation problems.

- [Differentiate tensor calculus](@ref "Tensor Calculus"), including tensor contractions, analytically, with symmetries.
- [Calculus of variations](@ref "Calculus of Variations") (differentiate with respect to paths).
- [Analytic back-propagation](@ref "Analytic Backpropagation"). 
- Complex differentiation without splitting into the real and imaginary parts.

These problems benefit from `CombDiff` because they are the same problem
through the lens of combinatory logic.  The problems distill down to
differentiating through two constructs:

- functions whose input and/or output are functions. For example, $f \mapsto (i \mapsto x \cdot f(i))$.
- functions whose input is captured. For example, $w \mapsto (f(w) \circ
  g(w))(x)$. This has to be differentiated *without partial evaluations*.

A few more things are within reach and are planned 

- Second quantized operators with indices such as $c_i^{\dagger}$ and the Wick contraction.
- Differentiate fixed points.

This is pre-alpha stage academic software. Things will break.

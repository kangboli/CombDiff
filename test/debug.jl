"""
The AD theory can be a bit abstract. Maybe a concrete example can help clarify?

Suppose you like to differentiate |ẋ|² with respect to x, where ẋ = A x.

You can somewhat easily do this by differentiating xᵀAᵀ⋅Ax, which gives you 2AᵀAx.  Doing this with AD would require differentiating ẋ = A x, and ∂ẋ / ∂x is ill defined. However, the pullback (without explaining what it is) is well defined as 𝒫(x → ẋ) = (x, k) → Aᵀk. The derivative of |ẋ|^2 is derived through the chain rule of pullbacks as ∇|ẋ| ≜ 𝒫(x → ẋ)(x, 𝒫(x → |x|²)(ẋ, 1)) = 𝒫(x → ẋ)(x, 2x) = 2AᵀAx.
"""

"""
DFT is practically the following constrained minimization problem.

E[ψ₁, ψ₂, …] = ∑ᵢⱼ ⟨ψᵢ, (T + A) ψⱼ⟩ + ∫ ϵxc(ρ(r), |∇ρ(r)|) dr,
s.t. ⟨ ψᵢ, ψⱼ⟩ = δᵢⱼ

- ψᵢ ∈ L² are single particle wave functions. The orthonormal constraint comes from the pauli exclusion principle. ρ(r) = ∑ᵢ|ψᵢ(r)|² is the electron density.
- ϵxc is an unknown function. Practically you fit it to data calculated with more accurate electronic structure methods (coupled cluster and quantum monte carlo) sometimes with Physical constrains.
- The main theorem of DFT is that there exists an ϵxc that makes the theory exact. This is what you see if you look up DFT, but it is practically irrelavant.
- T and A are linear operators. T is the ∇² so you can evaluate easily in Fourier basis.
- the matrix element of A is a liturature called the pseudopotential, which is not straightforward.
- you can solve the constrained minimization however you like, but the Chemists use the self consistent field iteration, which solves the KKT condition. This procedure is the most expensive step.
"""

"""
The energy of a molecule looks like this
Em[r₁, r₂, …] = min_{ψ₁, ψ₂ …} E[r₁, r₂,…, ψ₁, ψ₂, …]

The force on the ith atom is ∂ Em[r₁, r₂, …]/∂ rᵢ.  You calculate this to do molecular dynamics.  This is expensive, so they train a model to learn the force.  The key idea there is the notation of being equivariant so that permute the atoms of the same species or rotating the whole molecule doesn't change the energy.

This does not replace DFT. It replaces the force calculation for molecular dynamics, which used to be done with DFT. 
"""
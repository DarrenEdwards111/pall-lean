import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterIsotropicMinimization

/-!
# The directional derivative of the scale-invariant Forster potential `G` (rung 3, combined)

`…ForsterIsotropicMinimization` proves the two halves of rung 3's directional derivative separately:

* `hasDerivAt_potential` — the `F`-side, `d/dt ∑ᵢ log⟪vᵢ,(S+tΔ)vᵢ⟫|₀ = ∑ᵢ ⟪vᵢ,Δvᵢ⟫/⟪vᵢ,Svᵢ⟫`;
* `hasDerivAt_logdet` — the `log det`-side, `d/dt log det(S+tΔ)|₀ = tr(S⁻¹Δ)` (Jacobi along a line).

This file combines them into the directional derivative of the **scale-invariant** potential
`G(S) = F(S) − (m/d)·log det S` — the gradient whose vanishing in every direction at the minimizer `S⋆` is rung 3's
first-order optimality condition (the source of the Lagrange identity `∑ᵢ vᵢvᵢᵀ/⟪vᵢ,S⋆vᵢ⟫ = (m/d)·S⋆⁻¹`).  Pure
combination of the two proved derivative lemmas (`HasDerivAt.sub` / `.const_mul`); no `sorry`, no socket.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`; it is the next analytic rung of the Forster `∃T` grind.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForsterIsotropic

open scoped BigOperators Matrix

variable {d m : ℕ}

/-- **Rung 3c — the gradient of the scale-invariant potential.**  The directional derivative of
`G(S) = ∑ᵢ log⟪vᵢ,Svᵢ⟫ − (m/d)·log det S` along `t ↦ S + tΔ` at `t = 0` is
`(∑ᵢ ⟪vᵢ,Δvᵢ⟫/⟪vᵢ,Svᵢ⟫) − (m/d)·tr(S⁻¹Δ)` — the `F`-side (`hasDerivAt_potential`) minus `(m/d)` times the
`log det`-side (`hasDerivAt_logdet`).  Setting this to `0` for every symmetric `Δ` at the minimizer is rung 3's
first-order condition. -/
theorem hasDerivAt_G {S Δ : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin m → (Fin d → ℝ)} (hv : ∀ i, v i ≠ 0) :
    HasDerivAt (fun t : ℝ => potential v (S + t • Δ) - ((m : ℝ) / d) * Real.log (S + t • Δ).det)
      ((∑ i, (v i ⬝ᵥ (Δ *ᵥ v i)) / (v i ⬝ᵥ (S *ᵥ v i))) - ((m : ℝ) / d) * (S⁻¹ * Δ).trace) 0 :=
  (hasDerivAt_potential hS hv).sub ((hasDerivAt_logdet hS).const_mul ((m : ℝ) / d))

end PallLean.Paper93.DeepMath.PathB.ForsterIsotropic

#print axioms PallLean.Paper93.DeepMath.PathB.ForsterIsotropic.hasDerivAt_G

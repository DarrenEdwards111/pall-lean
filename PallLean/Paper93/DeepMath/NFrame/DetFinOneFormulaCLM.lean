import PallLean.Paper93.DeepMath.NFrame.DetFinOne
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Elementwise

/-!
# Explicit Fréchet derivative of the 1×1 determinant as a CLM composition

For a 1×1 real matrix `A : Matrix (Fin 1) (Fin 1) ℝ`, the determinant equals
`A 0 0`. Viewing the state space as the nested Pi type
`Fin 1 → Fin 1 → ℝ`, this is a composition of two coordinate
projections: first `A ↦ A 0 : Fin 1 → ℝ`, then `g ↦ g 0 : ℝ`.

The Fréchet derivative is given by the corresponding composition of
`ContinuousLinearMap.proj 0` at the two stages. This file packages that
explicit CLM as `detFinOneCLM` and proves
`HasFDerivAt Matrix.det detFinOneCLM A` at every 1×1 matrix `A`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The explicit continuous linear map that equals `fderiv ℝ Matrix.det A`
for 1×1 matrices: the double-projection `ΔA ↦ ΔA 0 0`. Built as
`(proj 0) ∘L (proj 0)` where the inner projection lands in `Fin 1 → ℝ`
and the outer one evaluates at `0`. -/
noncomputable def detFinOneCLM : Matrix (Fin 1) (Fin 1) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 1 → ℝ) (0 : Fin 1))

/-- At any 1×1 matrix `A`, `HasFDerivAt Matrix.det detFinOneCLM A`. -/
theorem hasFDerivAt_det_fin_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    HasFDerivAt (Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ) detFinOneCLM A := by
  -- Rewrite `det` as the double evaluation `A ↦ A 0 0` on 1×1 matrices.
  have h : (Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ) = (fun M => M 0 0) := by
    funext M
    exact Matrix.det_fin_one M
  rw [h]
  -- The inner projection `A ↦ A 0 : Matrix (Fin 1) (Fin 1) ℝ → Fin 1 → ℝ`.
  -- Matrix (Fin 1) (Fin 1) ℝ unfolds to `Fin 1 → Fin 1 → ℝ`, so the
  -- Pi-type projection CLM applies directly.
  have h_inner :
      HasFDerivAt (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 1 → ℝ)
          (0 : Fin 1)) A := by
    exact hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (A : Fin 1 → Fin 1 → ℝ)
  -- The outer projection `g ↦ g 0 : (Fin 1 → ℝ) → ℝ`, evaluated at `A 0`.
  have h_outer :
      HasFDerivAt (fun g : Fin 1 → ℝ => g 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ)
          (0 : Fin 1)) (A 0) := by
    exact hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (A 0)
  -- Chain rule: the composition is `(fun M => M 0 0)`, with derivative the
  -- composition of the two projection CLMs, which is `detFinOneCLM`.
  exact h_outer.comp A h_inner

end PallLean.Paper93.DeepMath.NFrame

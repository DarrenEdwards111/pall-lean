import PallLean.Paper93.DeepMath.NFrame.DetFinOne
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivative of the determinant on 1×1 matrices (scalar-time version)

For the identification `Matrix (Fin 1) (Fin 1) ℝ ≃ (Fin 1 → Fin 1 → ℝ)`,
`det` coincides with the double coordinate evaluation at `(0,0)`; hence for
any differentiable path `f : ℝ → Matrix (Fin 1) (Fin 1) ℝ` the scalar function
`s ↦ (f s).det` is differentiable with derivative `(df/ds) 0 0`.

This is the Jacobi-formula-style derivative in the degenerate `n = 1` case.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- If `f : ℝ → Matrix (Fin 1) (Fin 1) ℝ` is differentiable with derivative
`f'` at `t`, then `s ↦ (f s).det` has derivative `f' 0 0` at `t`.  This is the
`n = 1` specialisation of the Jacobi formula: the determinant on `1 × 1`
matrices is the linear coordinate `A ↦ A 0 0`, so its derivative along a path
is just the `(0,0)` entry of the path's derivative. -/
theorem det_fin_one_hasDerivAt_of_scalar
    (f : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ) (f' : Matrix (Fin 1) (Fin 1) ℝ)
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).det) (f' 0 0) t := by
  -- Reduce the determinant on 1×1 matrices to the `(0,0)` evaluation.
  have h_eq : (fun s => (f s).det) = (fun s => (f s) 0 0) := by
    funext s
    exact Matrix.det_fin_one (f s)
  rw [h_eq]
  -- Step 1: `s ↦ f s 0` has derivative `f' 0` at `t`.
  -- Here the outer map is the evaluation `g ↦ g 0` on `Fin 1 → Fin 1 → ℝ`,
  -- whose Fréchet derivative is the projection CLM `proj 0`.
  have hproj_outer :
      HasFDerivAt (fun g : Fin 1 → Fin 1 → ℝ => g 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 1 → ℝ)
          (0 : Fin 1))
        (f t) := by
    exact hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (f t)
  have h1 : HasDerivAt (fun s => f s 0) (f' 0) t :=
    hproj_outer.comp_hasDerivAt t hf
  -- Step 2: `s ↦ (f s) 0 0` has derivative `(f' 0) 0 = f' 0 0` at `t`.
  have hproj_inner :
      HasFDerivAt (fun g : Fin 1 → ℝ => g 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ)
          (0 : Fin 1))
        (f t 0) := by
    exact hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (f t 0)
  have h2 : HasDerivAt ((fun g : Fin 1 → ℝ => g 0) ∘ (fun s => f s 0)) (f' 0 0) t :=
    hproj_inner.comp_hasDerivAt t h1
  -- Unfold the composition: `((fun g => g 0) ∘ (fun s => f s 0)) s = (f s) 0 0`.
  exact h2

end PallLean.Paper93.DeepMath.NFrame

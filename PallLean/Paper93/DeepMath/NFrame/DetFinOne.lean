import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Elementwise

/-!
# Determinant of a 1×1 matrix (N-Frame)

This file isolates the `n = 1` specialisation of the determinant function
on real matrices. For a `1 × 1` matrix `A`, Mathlib provides
`Matrix.det_fin_one : A.det = A 0 0`. We package this as a pointwise
equality, a function-level equality, and use it to derive that
`Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ` is differentiable everywhere
(it is a linear coordinate projection of a finite-dimensional space).

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a 1×1 matrix, `det A = A 0 0`. -/
theorem det_fin_one_eq (A : Matrix (Fin 1) (Fin 1) ℝ) : A.det = A 0 0 := by
  exact Matrix.det_fin_one A

/-- The determinant on `Matrix (Fin 1) (Fin 1) ℝ` equals the evaluation at `(0,0)`. -/
theorem det_fin_one_eq_fun :
    (Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ) = (fun A => A 0 0) := by
  funext A
  exact Matrix.det_fin_one A

/-- 1×1 det is differentiable.

The map `A ↦ A 0 0` on `Matrix (Fin 1) (Fin 1) ℝ = Fin 1 → Fin 1 → ℝ` is
the composition of two coordinate projections (each an evaluation
`differentiable_apply 0`), hence differentiable. -/
theorem det_fin_one_differentiable :
    Differentiable ℝ (Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ) := by
  rw [det_fin_one_eq_fun]
  -- Outer evaluation: `fun f : Fin 1 → ℝ => f 0` is differentiable.
  have h_outer : Differentiable ℝ (fun f : Fin 1 → ℝ => f 0) :=
    differentiable_apply (0 : Fin 1)
  -- Inner evaluation: `fun A : Matrix (Fin 1) (Fin 1) ℝ => A 0` is differentiable,
  -- viewing `Matrix (Fin 1) (Fin 1) ℝ` as `Fin 1 → Fin 1 → ℝ`.
  have h_inner : Differentiable ℝ
      (fun A : Matrix (Fin 1) (Fin 1) ℝ => A 0) :=
    differentiable_apply (0 : Fin 1)
  -- Composition yields `A ↦ (A 0) 0 = A 0 0`.
  exact h_outer.comp h_inner

end PallLean.Paper93.DeepMath.NFrame

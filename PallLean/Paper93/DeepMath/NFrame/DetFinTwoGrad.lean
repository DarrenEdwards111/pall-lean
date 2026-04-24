import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Elementwise

/-!
# Determinant of a 2×2 matrix and its differentiability (N-Frame)

This file isolates the `n = 2` specialisation of the determinant function
on real matrices. For a `2 × 2` matrix `A`, Mathlib provides
`Matrix.det_fin_two : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0`.
We package this as a pointwise equality and use it to derive that
`Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ` is differentiable everywhere.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a 2×2 matrix, `det A = A 0 0 * A 1 1 - A 0 1 * A 1 0`. -/
theorem det_fin_two_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 :=
  Matrix.det_fin_two A

/-- 2×2 det is differentiable.

The map `A ↦ A 0 0 * A 1 1 - A 0 1 * A 1 0` is a polynomial in four
coordinate projections of `Matrix (Fin 2) (Fin 2) ℝ = Fin 2 → Fin 2 → ℝ`,
each of which is differentiable by `differentiable_apply`. Sum/product
combinators preserve differentiability. -/
theorem det_fin_two_differentiable :
    Differentiable ℝ (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ) := by
  have h : (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ) =
    (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0 * A 1 1 - A 0 1 * A 1 0) := by
    funext A; exact Matrix.det_fin_two A
  rw [h]
  -- Entry `A i j` as a composition of two `differentiable_apply`s.
  have hentry : ∀ i j : Fin 2,
      Differentiable ℝ (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) := by
    intro i j
    have h1 : Differentiable ℝ (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i) :=
      differentiable_apply i
    have h2 : Differentiable ℝ (fun f : Fin 2 → ℝ => f j) :=
      differentiable_apply j
    exact h2.comp h1
  apply Differentiable.sub
  · exact (hentry 0 0).mul (hentry 1 1)
  · exact (hentry 0 1).mul (hentry 1 0)

end PallLean.Paper93.DeepMath.NFrame

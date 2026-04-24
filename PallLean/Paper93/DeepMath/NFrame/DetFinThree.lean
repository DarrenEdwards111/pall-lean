import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Elementwise

/-!
# Determinant of a 3×3 matrix and its differentiability (N-Frame)

This file isolates the `n = 3` specialisation of the determinant function
on real matrices. For a `3 × 3` matrix `A`, Mathlib provides
`Matrix.det_fin_three`, which expands the determinant as a sum/difference
of six cubic monomials in the nine entries of `A`. We package this as a
pointwise equality and derive that
`Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ` is differentiable everywhere.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Explicit 3×3 determinant formula from Mathlib. -/
theorem det_fin_three_eq (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.det = A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
         - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
         + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := by
  rw [Matrix.det_fin_three]

/-- 3×3 det is differentiable (polynomial in entries).

The map `A ↦ det A` equals a polynomial expression in the nine coordinate
projections of `Matrix (Fin 3) (Fin 3) ℝ = Fin 3 → Fin 3 → ℝ`, each of
which is differentiable by `differentiable_apply`. Sum, difference and
product combinators then preserve differentiability. -/
theorem det_fin_three_differentiable :
    Differentiable ℝ (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ) := by
  -- Entry `A i j` as a composition of two `differentiable_apply`s.
  have entry : ∀ (i j : Fin 3),
      Differentiable ℝ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) := by
    intro i j
    have h1 : Differentiable ℝ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i) :=
      differentiable_apply i
    have h2 : Differentiable ℝ (fun f : Fin 3 → ℝ => f j) :=
      differentiable_apply j
    exact h2.comp h1
  have h : (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ) = fun A =>
    A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
    - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
    + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := by
    funext A; exact det_fin_three_eq A
  rw [h]
  -- Build each of the six monomials, then combine with ±.
  have t1 : Differentiable ℝ
      (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 0 * A 1 1 * A 2 2) :=
    ((entry 0 0).mul (entry 1 1)).mul (entry 2 2)
  have t2 : Differentiable ℝ
      (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 0 * A 1 2 * A 2 1) :=
    ((entry 0 0).mul (entry 1 2)).mul (entry 2 1)
  have t3 : Differentiable ℝ
      (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 1 * A 1 0 * A 2 2) :=
    ((entry 0 1).mul (entry 1 0)).mul (entry 2 2)
  have t4 : Differentiable ℝ
      (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 1 * A 1 2 * A 2 0) :=
    ((entry 0 1).mul (entry 1 2)).mul (entry 2 0)
  have t5 : Differentiable ℝ
      (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 2 * A 1 0 * A 2 1) :=
    ((entry 0 2).mul (entry 1 0)).mul (entry 2 1)
  have t6 : Differentiable ℝ
      (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 2 * A 1 1 * A 2 0) :=
    ((entry 0 2).mul (entry 1 1)).mul (entry 2 0)
  exact (((((t1.sub t2).sub t3).add t4).add t5).sub t6)

end PallLean.Paper93.DeepMath.NFrame

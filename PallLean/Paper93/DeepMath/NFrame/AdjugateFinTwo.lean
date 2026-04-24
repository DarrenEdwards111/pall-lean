import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic

/-!
# Explicit 2×2 adjugate formulas (N-Frame)

This file specialises Mathlib's `Matrix.adjugate_fin_two` to the real case
and records the four entry-wise formulas as named lemmas for later use.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Explicit 2×2 adjugate: `adj A = !![A 1 1, -A 0 1; -A 1 0, A 0 0]`. -/
theorem adjugate_fin_two_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.adjugate = !![A 1 1, -A 0 1; -A 1 0, A 0 0] :=
  Matrix.adjugate_fin_two A

/-- 2×2 adjugate entry `(0,0)`. -/
theorem adjugate_fin_two_entry_00 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.adjugate 0 0 = A 1 1 := by
  rw [adjugate_fin_two_eq]; rfl

/-- 2×2 adjugate entry `(1,1)`. -/
theorem adjugate_fin_two_entry_11 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.adjugate 1 1 = A 0 0 := by
  rw [adjugate_fin_two_eq]; rfl

/-- 2×2 adjugate entry `(0,1)`. -/
theorem adjugate_fin_two_entry_01 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.adjugate 0 1 = -A 0 1 := by
  rw [adjugate_fin_two_eq]; rfl

/-- 2×2 adjugate entry `(1,0)`. -/
theorem adjugate_fin_two_entry_10 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.adjugate 1 0 = -A 1 0 := by
  rw [adjugate_fin_two_eq]; rfl

end PallLean.Paper93.DeepMath.NFrame

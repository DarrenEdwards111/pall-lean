import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Cofactor expansion of the determinant (N-Frame)

This file provides thin wrappers around Mathlib's Laplacian/cofactor
expansion theorems for determinants of `(n+1) × (n+1)` matrices over `ℝ`.

* `det_succ_row_zero` expands the determinant along row `0`.
* `det_succ_column_zero` expands the determinant along column `0`.

Both are direct specialisations of the corresponding Mathlib theorems
`Matrix.det_succ_row_zero` / `Matrix.det_succ_column_zero`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Cofactor expansion along row 0 (wraps Mathlib's `Matrix.det_succ_row_zero`). -/
theorem det_succ_row_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.det = ∑ j : Fin (n + 1),
      (-1)^(j : ℕ) * A 0 j * (A.submatrix Fin.succ j.succAbove).det := by
  exact Matrix.det_succ_row_zero A

/-- Cofactor expansion along column 0 (wraps Mathlib's `Matrix.det_succ_column_zero`). -/
theorem det_succ_column_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.det = ∑ i : Fin (n + 1),
      (-1)^(i : ℕ) * A i 0 * (A.submatrix i.succAbove Fin.succ).det := by
  exact Matrix.det_succ_column_zero A

end PallLean.Paper93.DeepMath.NFrame

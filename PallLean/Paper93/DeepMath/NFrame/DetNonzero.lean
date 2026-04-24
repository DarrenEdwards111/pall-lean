import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Nonzero determinant facts for N-Frame barrier

Two small wrappers used by the N-Frame log-det barrier:

* `det_ne_zero_of_isUnit`: an invertible matrix has nonzero determinant.
* `matrix_ne_zero_of_det_pos`: a positive-determinant matrix is nonzero
  (stated for `1 ≤ n`, since in dimension zero every matrix is the
  unique empty matrix with determinant `1`, so the zero matrix itself
  has positive determinant there).

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- An invertible matrix has nonzero determinant
(wraps Mathlib's `Matrix.isUnit_iff_isUnit_det`). -/
theorem det_ne_zero_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit A) : A.det ≠ 0 := by
  have hUnit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h
  exact hUnit.ne_zero

/-- A positive-determinant matrix is nonzero (for `1 ≤ n`).

The dimension hypothesis is needed because `Matrix.det_zero` requires
`Nonempty n`; in dimension zero, every matrix (including the zero
matrix) is the unique empty matrix with determinant `1`. -/
theorem matrix_ne_zero_of_det_pos {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (h : 0 < A.det) : A ≠ 0 := by
  intro hA
  -- From `A = 0` and `Nonempty (Fin n)` we get `det A = 0`, contradicting `0 < det A`.
  have hNE : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdet0 : (0 : Matrix (Fin n) (Fin n) ℝ).det = 0 :=
    Matrix.det_zero hNE
  have : A.det = 0 := by rw [hA]; exact hdet0
  exact (lt_irrefl (0 : ℝ)) (this ▸ h)

end PallLean.Paper93.DeepMath.NFrame

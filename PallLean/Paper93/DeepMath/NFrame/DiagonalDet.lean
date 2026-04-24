import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Determinant of a diagonal matrix (N-Frame)

Packaging of three small facts about the determinant of a real diagonal
matrix:

* `det_diagonal_eq`: the determinant equals the product of the diagonal
  entries.
* `det_diagonal_pos`: if every diagonal entry is strictly positive, so is
  the determinant.
* `log_det_diagonal_pos`: for strictly positive diagonal entries, the
  logarithm of the determinant equals the sum of the logarithms.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Determinant of diagonal matrix is product of diagonal entries. -/
theorem det_diagonal_eq {n : ℕ} (d : Fin n → ℝ) :
    (Matrix.diagonal d).det = ∏ i, d i := by
  exact Matrix.det_diagonal

/-- For positive diagonal entries, the determinant is positive. -/
theorem det_diagonal_pos {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) :
    0 < (Matrix.diagonal d).det := by
  rw [det_diagonal_eq]
  exact Finset.prod_pos fun i _ => h i

/-- `log` of determinant of positive-diagonal matrix is sum of logs. -/
theorem log_det_diagonal_pos {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) :
    Real.log (Matrix.diagonal d).det = ∑ i, Real.log (d i) := by
  rw [det_diagonal_eq, Real.log_prod]
  intros i _
  exact (h i).ne'

end PallLean.Paper93.DeepMath.NFrame

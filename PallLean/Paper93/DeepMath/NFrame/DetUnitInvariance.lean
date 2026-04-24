import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Determinant under unit-`det²` conjugation (N-Frame)

Two small wrappers about the determinant of a conjugation
`Uᵀ A U`:

* `det_conj_eq_det_sq_mul`: `det(Uᵀ A U) = (det U)² · det A`.
* `det_conj_invariant_of_unit_det_sq`: if `(det U)² = 1` then
  `det(Uᵀ A U) = det A`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `det(Uᵀ A U) = (det U)² · det A`. -/
theorem det_conj_eq_det_sq_mul {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℝ) :
    (U.transpose * A * U).det = U.det^2 * A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- For U with det²= 1, `det(Uᵀ A U) = det A`. -/
theorem det_conj_invariant_of_unit_det_sq {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.det^2 = 1) :
    (U.transpose * A * U).det = A.det := by
  rw [det_conj_eq_det_sq_mul U A, hU, one_mul]

end PallLean.Paper93.DeepMath.NFrame

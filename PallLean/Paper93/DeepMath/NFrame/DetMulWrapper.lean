import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# Determinant multiplicative / transpose / inverse wrappers (N-Frame)

Thin Mathlib wrappers providing:

* `det_mul_prod`  : `det (A * B) = det A * det B`.
* `det_transpose_eq` : `det Aᵀ = det A`.
* `det_inv_of_invertible` : `det A⁻¹ = (det A)⁻¹` when `A.det` is a unit.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `det(A · B) = det A · det B`. -/
theorem det_mul_prod {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).det = A.det * B.det := Matrix.det_mul A B

/-- `det(Aᵀ) = det A`. -/
theorem det_transpose_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.transpose.det = A.det := Matrix.det_transpose A

/-- `det(A⁻¹) = (det A)⁻¹` for invertible `A` (i.e. when `A.det` is a unit).

On `ℝ` (a `GroupWithZero`), `Ring.inverse` coincides with `Inv.inv`, so the
general Mathlib identity `Matrix.det_nonsing_inv` specialises to the
stated form. -/
theorem det_inv_of_invertible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (_h : IsUnit A.det) :
    A⁻¹.det = (A.det)⁻¹ := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

end PallLean.Paper93.DeepMath.NFrame

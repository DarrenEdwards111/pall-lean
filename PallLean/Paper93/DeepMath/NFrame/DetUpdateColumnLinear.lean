import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Linearity of the determinant in a single column

This file exposes the bilinear-in-each-column property of the determinant
specialised to a single column update: namely, that updating column `j`
with `a • u + b • v` produces a determinant equal to
`a * det(... u ...) + b * det(... v ...)`.

The proof is a direct combination of Mathlib's `Matrix.det_updateCol_add`
and `Matrix.det_updateCol_smul`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Det is linear in the j-th column. -/
theorem det_update_col_linear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (a b : ℝ) (u v : Fin n → ℝ) :
    (A.updateCol j (a • u + b • v)).det
      = a * (A.updateCol j u).det + b * (A.updateCol j v).det := by
  rw [Matrix.det_updateCol_add, Matrix.det_updateCol_smul, Matrix.det_updateCol_smul]

end PallLean.Paper93.DeepMath.NFrame

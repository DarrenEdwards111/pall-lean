import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Determinant of a scalar multiple (N-Frame)

This file packages the standard Mathlib identity
`Matrix.det_smul : det (c • A) = c ^ Fintype.card n * det A`
in the special case of square real matrices indexed by `Fin n`,
so that the exponent appears as the plain natural number `n`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Determinant of a scalar multiple: `det (c • M) = c ^ n * det M`. -/
theorem det_smul {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (c • M).det = c ^ n * M.det := by
  rw [Matrix.det_smul M c, Fintype.card_fin]

end PallLean.Paper93.DeepMath.NFrame

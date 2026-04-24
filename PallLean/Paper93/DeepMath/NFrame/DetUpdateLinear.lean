import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Row-linearity of the determinant (N-Frame)

This file packages the multilinearity of the determinant in a given row:
if row `i` of `A` is replaced by a linear combination `a • u + b • v`, then
the resulting determinant is the corresponding linear combination of the
determinants obtained by replacing row `i` with `u` or `v` separately.

We combine Mathlib's two separable lemmas:
* `Matrix.det_updateRow_add` for additivity of `updateRow` in the row,
* `Matrix.det_updateRow_smul` for scalar multiplicativity in the row.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `det` is linear in row `i`: updating row `i` to a linear combination
`a • u + b • v` gives a corresponding linear combination of determinants.
Combines `Matrix.det_updateRow_add` and `Matrix.det_updateRow_smul`. -/
theorem det_update_row_linear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (a b : ℝ) (u v : Fin n → ℝ) :
    (A.updateRow i (a • u + b • v)).det
      = a * (A.updateRow i u).det + b * (A.updateRow i v).det := by
  rw [Matrix.det_updateRow_add A i (a • u) (b • v),
      Matrix.det_updateRow_smul A i a u,
      Matrix.det_updateRow_smul A i b v]

end PallLean.Paper93.DeepMath.NFrame

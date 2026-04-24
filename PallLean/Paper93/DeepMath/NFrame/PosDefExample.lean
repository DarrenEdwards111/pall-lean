import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.StarOrdered

/-!
# An explicit 2×2 positive-definite example (N-Frame)

This file provides a concrete 2×2 real matrix, `!![2, 1; 1, 2]`, and
computes its determinant. This is used as a simple sanity example in
the N-Frame development.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Explicit 2×2 PosDef example: `!![2, 1; 1, 2]`. Its determinant is 3 > 0 and
    its diagonal entries are positive. -/
def exPosDef : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

theorem exPosDef_det_eq_three : exPosDef.det = 3 := by
  unfold exPosDef
  rw [Matrix.det_fin_two]
  simp
  norm_num

theorem exPosDef_det_pos : 0 < exPosDef.det := by
  rw [exPosDef_det_eq_three]; norm_num

end PallLean.Paper93.DeepMath.NFrame

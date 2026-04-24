import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.StarOrdered

/-!
# The identity matrix is positive definite (N-Frame)

This file packages two trivial facts about the `n × n` real identity
matrix that are used elsewhere in the N-Frame development:

* `one_posDef`: the identity matrix `1` is positive definite.
* `one_det`: `det(1) = 1`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The identity matrix is positive definite. -/
theorem one_posDef {n : ℕ} : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef :=
  Matrix.PosDef.one

/-- `det(1) = 1` (reminder wrapper). -/
theorem one_det {n : ℕ} : (1 : Matrix (Fin n) (Fin n) ℝ).det = 1 :=
  Matrix.det_one

end PallLean.Paper93.DeepMath.NFrame

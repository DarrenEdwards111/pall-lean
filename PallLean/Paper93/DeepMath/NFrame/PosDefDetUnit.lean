import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# PosDef matrices are units (N-Frame)

Two small wrappers stating that a real symmetric positive-definite
matrix is invertible at the level of both its determinant and the
matrix itself:

* `posDef_det_isUnit`: `IsUnit A.det` whenever `A.PosDef`.
* `posDef_isUnit`: `IsUnit A` whenever `A.PosDef`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- A PosDef matrix has nonzero determinant, hence is a unit. -/
theorem posDef_det_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    IsUnit A.det :=
  hA.det_pos.ne'.isUnit

/-- A PosDef matrix is invertible (as a matrix). -/
theorem posDef_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact posDef_det_isUnit A hA

end PallLean.Paper93.DeepMath.NFrame

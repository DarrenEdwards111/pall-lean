import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB

/-- Definition: the identity minor of A at index set J equals 1.
    In paper §7.1, this is the amplituhedron preservation property. -/
def HasUnitMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (J : Fin k → Fin n) : Prop :=
  (A.submatrix J J).det = 1

/-- Trivially: identity matrix has unit minor at any J. -/
theorem identity_hasUnitMinor {n k : ℕ} (J : Fin k → Fin n)
    (hInj : Function.Injective J) :
    HasUnitMinor (1 : Matrix (Fin n) (Fin n) ℝ) J := by
  unfold HasUnitMinor
  rw [Matrix.submatrix_one J hInj]
  exact Matrix.det_one

end PallLean.Paper93.DeepMath.PathB

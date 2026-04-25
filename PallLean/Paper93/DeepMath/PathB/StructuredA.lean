import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.DiagonalUnitMinor

namespace PallLean.Paper93.DeepMath.PathB

/-- A matrix A is "structured" with respect to a singleton family `{J}` if the principal
    minor at J equals 1. -/
def IsStructuredAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (J : Fin k → Fin n) : Prop :=
  (A.submatrix J J).det = 1

/-- Identity matrix has det = 1 for any injective J (its submatrix is identity on Fin k). -/
theorem identity_isStructured_at {n k : ℕ} (J : Fin k → Fin n) (hInj : Function.Injective J) :
    IsStructuredAt (1 : Matrix (Fin n) (Fin n) ℝ) J := by
  unfold IsStructuredAt
  rw [Matrix.submatrix_one J hInj]
  exact Matrix.det_one

end PallLean.Paper93.DeepMath.PathB

import PallLean.Paper93.DeepMath.NFrame.DetFinThree

namespace PallLean.Paper93.DeepMath.NFrame

/-- Partial of 3×3 det in entry (0,0): `∂/∂(A 0 0) det = A 1 1 · A 2 2 − A 1 2 · A 2 1`
    (the (0,0)-cofactor). -/
theorem det_fin_three_partial_at_00 (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.det = A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1)
          + A 0 1 * (- (A 1 0 * A 2 2 - A 1 2 * A 2 0))
          + A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0) := by
  rw [det_fin_three_eq]
  ring

end PallLean.Paper93.DeepMath.NFrame

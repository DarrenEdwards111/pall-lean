import PallLean.Paper93.DeepMath.NFrame.MatrixClosedBallCompact
import PallLean.Paper93.DeepMath.NFrame.PosDefClosedSubset

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- The intersection of a closed det-interval and a closed ball in matrix space is compact. -/
theorem isCompact_detInterval_closedBall {n : ℕ}
    (c C R : ℝ) (A₀ : Matrix (Fin n) (Fin n) ℝ) :
    IsCompact (Metric.closedBall A₀ R ∩ {A : Matrix (Fin n) (Fin n) ℝ | c ≤ A.det ∧ A.det ≤ C}) := by
  apply IsCompact.inter_right
  · exact matrix_closedBall_isCompact A₀ R
  · exact isClosed_det_interval c C

end PallLean.Paper93.DeepMath.NFrame

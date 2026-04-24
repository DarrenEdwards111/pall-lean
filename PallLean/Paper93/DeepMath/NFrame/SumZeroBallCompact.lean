import PallLean.Paper93.DeepMath.NFrame.SumZeroSubspace
import PallLean.Paper93.DeepMath.NFrame.FiniteDimCompact

namespace PallLean.Paper93.DeepMath.NFrame

/-- Intersection of the sum-zero subspace with the closed ball of radius R
    is compact (closed bounded subset of finite-dim ℝⁿ, Heine-Borel). -/
theorem sumZeroBall_compact {n : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (Metric.closedBall (0 : Fin n → ℝ) R ∩
               {phi : Fin n → ℝ | ∑ i, phi i = 0}) := by
  -- closed ball ∩ closed = closed; and intersection with compact (the ball) is compact
  apply IsCompact.inter_right
  · exact isCompact_closedBall R hR
  · exact sumZeroSubspace_isClosed

end PallLean.Paper93.DeepMath.NFrame

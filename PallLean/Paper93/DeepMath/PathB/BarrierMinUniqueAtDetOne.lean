import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.LogNonposIff

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For PosDef M with det M ≤ 1: barrier M ≥ 0, with equality iff det M = 1.
    This means the minimum of barrier on the constraint set {M : PosDef ∧ det M ≤ 1}
    is attained exactly when det M = 1. -/
theorem barrier_zero_iff_det_one_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hPos : 0 < M.det) (hDet : M.det ≤ 1) :
    barrier M = 0 ↔ M.det = 1 := by
  unfold barrier
  constructor
  · intro h
    have hlog : Real.log M.det = 0 := by linarith
    have := (log_nonpos_iff_le_one hPos).mp (le_of_eq hlog)
    -- log_eq_zero gives det = 1 (since det > 0, det ≠ -1)
    rcases Real.log_eq_zero.mp hlog with h0 | h1 | hm1
    · exact absurd h0 (ne_of_gt hPos)
    · exact h1
    · linarith [hPos]
  · intro h
    rw [h, Real.log_one]; ring

end PallLean.Paper93.DeepMath.PathB

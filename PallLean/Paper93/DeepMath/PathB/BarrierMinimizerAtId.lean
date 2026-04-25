import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.IdentityPosDef

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- The barrier function `barrier(M) = -log(det M)` is minimized over PosDef M with `det M ≤ 1`
    when M = identity (where barrier = 0 = log 1). For matrices with det ≤ 1, barrier ≥ 0;
    at identity, barrier = 0. -/
theorem barrier_min_at_identity_when_det_le_one {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hPos : 0 < M.det) (hDet : M.det ≤ 1) :
    barrier (1 : Matrix (Fin n) (Fin n) ℝ) ≤ barrier M := by
  unfold barrier
  rw [Matrix.det_one, Real.log_one]
  have h_log : Real.log M.det ≤ 0 := Real.log_nonpos hPos.le hDet
  linarith

end PallLean.Paper93.DeepMath.PathB

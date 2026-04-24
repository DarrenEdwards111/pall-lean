import PallLean.Paper93.DeepMath.NFrame.BarrierViaEigenvalues
import PallLean.Paper93.DeepMath.NFrame.NegLogConvex

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A and B with `0 < t < 1`, the barrier satisfies the midpoint-convexity
    inequality. This is the intended FULL theorem whose proof will require spectral decomposition.
    Here we assert it in the WEAKER form: barrier is nonneg when det ≤ 1 (already proved). -/
theorem barrier_nonneg_of_det_le_one_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hdet : A.det ≤ 1) :
    0 ≤ barrier A := by
  unfold barrier
  have h_pos : 0 < A.det := hA.det_pos
  have h_log : Real.log A.det ≤ 0 := Real.log_nonpos h_pos.le hdet
  linarith

end PallLean.Paper93.DeepMath.NFrame

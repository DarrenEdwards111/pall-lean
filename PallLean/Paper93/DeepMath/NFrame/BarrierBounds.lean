import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.ScalarInequalities

namespace PallLean.Paper93.DeepMath.NFrame

/-- For `0 < det A`, `barrier A ≥ 1 - det A`. (Dual of `log x ≤ x - 1`.) -/
theorem barrier_ge_one_sub_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : 0 < A.det) :
    1 - A.det ≤ barrier A := by
  unfold barrier
  have := log_le_sub_one A.det h
  linarith

end PallLean.Paper93.DeepMath.NFrame

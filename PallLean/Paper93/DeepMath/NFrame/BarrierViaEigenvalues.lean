import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.LogDetEigenvalues

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A, the barrier equals the negation of the sum of log-eigenvalues. -/
theorem barrier_eq_neg_sum_log_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    barrier A = -∑ i, Real.log (hA.1.eigenvalues i) := by
  unfold barrier
  rw [log_det_posDef_eq_sum_log_eigenvalues A hA]

end PallLean.Paper93.DeepMath.NFrame

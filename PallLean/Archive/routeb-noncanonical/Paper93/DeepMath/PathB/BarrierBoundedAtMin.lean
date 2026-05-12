import PallLean.Paper93.DeepMath.NFrame.BarrierBoundsViaEigenvalues
import PallLean.Paper93.DeepMath.NFrame.PosDefEigenvalues

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A, the barrier `-log(det A)` equals the negative sum of log-eigenvalues. -/
theorem barrier_eigenvalue_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    barrier A = -∑ i, Real.log (hA.1.eigenvalues i) :=
  barrier_eq_neg_sum_log_eigenvalues A hA

/-- At identity, barrier = 0 since all eigenvalues are 1. -/
theorem barrier_identity {n : ℕ} : barrier (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold barrier
  rw [Matrix.det_one, Real.log_one]
  ring

end PallLean.Paper93.DeepMath.PathB

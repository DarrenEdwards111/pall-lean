import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetSmul

namespace PallLean.Paper93.DeepMath.NFrame

/-- Barrier under scalar scaling: `barrier(c • A) = barrier A - n · log c` for c > 0. -/
theorem barrier_smul_pos {n : ℕ} (c : ℝ) (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : 0 < A.det) :
    barrier (c • A) = barrier A - n * Real.log c := by
  unfold barrier
  rw [det_smul]
  have hpow : 0 < c ^ n := pow_pos hc n
  rw [Real.log_mul (ne_of_gt hpow) (ne_of_gt hA)]
  rw [Real.log_pow]
  ring

end PallLean.Paper93.DeepMath.NFrame

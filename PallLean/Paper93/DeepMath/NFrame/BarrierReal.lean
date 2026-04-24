import PallLean.Paper93.DeepMath.NFrame.Barrier

namespace PallLean.Paper93.DeepMath.NFrame

/-- The barrier is a real number (trivially). -/
theorem barrier_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ r : ℝ, barrier A = r := ⟨barrier A, rfl⟩

/-- Barrier is a well-defined real number for any matrix A — follows trivially from definition. -/
theorem barrier_real_valued {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    barrier A = -Real.log A.det := rfl

/-- Barrier sign decomposition: `barrier A ≤ 0 ↔ log(det A) ≥ 0`. -/
theorem barrier_nonpos_iff_log_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    barrier A ≤ 0 ↔ 0 ≤ Real.log A.det := by
  unfold barrier
  constructor
  · intro h; linarith
  · intro h; linarith

end PallLean.Paper93.DeepMath.NFrame

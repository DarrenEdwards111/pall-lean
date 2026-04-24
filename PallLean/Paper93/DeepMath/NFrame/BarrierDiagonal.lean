import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DiagonalDet

namespace PallLean.Paper93.DeepMath.NFrame

/-- `barrier (diagonal d) = -∑ log (d i)` for positive diagonal d. -/
theorem barrier_diagonal_pos {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) :
    barrier (Matrix.diagonal d) = -∑ i, Real.log (d i) := by
  unfold barrier
  rw [log_det_diagonal_pos d h]

/-- Barrier at identity equals 0 (as sum version). -/
theorem barrier_diagonal_ones {n : ℕ} :
    barrier (Matrix.diagonal (fun _ : Fin n => (1 : ℝ))) = 0 := by
  rw [barrier_diagonal_pos _ (fun _ => zero_lt_one)]
  simp

end PallLean.Paper93.DeepMath.NFrame

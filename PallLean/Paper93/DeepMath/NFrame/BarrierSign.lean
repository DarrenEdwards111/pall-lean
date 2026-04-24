import PallLean.Paper93.DeepMath.NFrame.Barrier
import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A: `barrier A ≥ 0 ↔ det A ≤ 1`. -/
theorem barrier_nonneg_iff_det_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    0 ≤ barrier A ↔ A.det ≤ 1 := by
  unfold barrier
  have h_pos : 0 < A.det := hA.det_pos
  constructor
  · intro h
    have hlog : Real.log A.det ≤ 0 := by linarith
    exact (Real.log_nonpos_iff h_pos.le).mp hlog
  · intro h
    have hlog : Real.log A.det ≤ 0 := Real.log_nonpos h_pos.le h
    linarith

end PallLean.Paper93.DeepMath.NFrame

import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.LogNonposIff
import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A: `barrier A = 0 ↔ det A = 1`. -/
theorem barrier_zero_iff_det_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    barrier A = 0 ↔ A.det = 1 := by
  unfold barrier
  have h_pos : 0 < A.det := hA.det_pos
  constructor
  · intro h
    have hlog : Real.log A.det = 0 := by linarith
    exact (Real.log_eq_zero.mp hlog).resolve_left (ne_of_gt h_pos) |>.resolve_right
      (by intro hneg; linarith)
  · intro h
    rw [h, Real.log_one]
    ring

end PallLean.Paper93.DeepMath.NFrame

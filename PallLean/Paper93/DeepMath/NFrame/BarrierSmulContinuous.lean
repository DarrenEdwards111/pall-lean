import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.BarrierContinuous

namespace PallLean.Paper93.DeepMath.NFrame

/-- For `lam > 0`, `lam • barrier` continuous on `{A | det A > 0}`. -/
theorem lam_barrier_continuousOn (lam : ℝ) {n : ℕ} :
    ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => lam * barrier A)
                 {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} := by
  exact continuousOn_const.mul barrier_continuousOn_det_pos

end PallLean.Paper93.DeepMath.NFrame

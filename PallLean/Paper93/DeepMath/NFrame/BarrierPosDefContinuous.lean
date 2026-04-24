import PallLean.Paper93.DeepMath.NFrame.BarrierContinuous
import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.NFrame

/-- Barrier is continuous at every PosDef matrix. -/
theorem barrier_continuousAt_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ContinuousAt (fun B => barrier B) A :=
  barrier_continuousAt_of_det_pos A hA.det_pos

/-- Barrier is continuous on the set of PosDef matrices. -/
theorem barrier_continuousOn_posDef {n : ℕ} :
    ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => barrier A)
                 {A | A.PosDef} := by
  intros A hA
  exact (barrier_continuousAt_posDef A hA).continuousWithinAt

end PallLean.Paper93.DeepMath.NFrame

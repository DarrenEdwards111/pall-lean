import PallLean.Paper93.DeepMath.NFrame.BarrierDivergence
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
namespace NFrameAnalyticStepAudit
open PallLean.Paper93.DeepMath.NFrame

theorem barrier_drop_eq_log_det_ratio {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : 0 < A.det) (hB : 0 < B.det) :
    barrier A - barrier B = Real.log (B.det / A.det) := by
  rw [Real.log_div (ne_of_gt hB) (ne_of_gt hA)]
  unfold barrier
  ring

theorem barrier_drop_le_of_det_ratio_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hA : 0 < A.det) (hB : 0 < B.det)
    (hstep : B.det / A.det ≤ Real.exp r) :
    barrier A - barrier B ≤ r := by
  rw [barrier_drop_eq_log_det_ratio A B hA hB]
  have h := Real.log_le_log (div_pos hB hA) hstep
  simpa using h

theorem singular_barrier_value {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det = 0) :
    barrier A = 0 := by
  simp [barrier, hA]

end NFrameAnalyticStepAudit
#print axioms NFrameAnalyticStepAudit.barrier_drop_eq_log_det_ratio
#print axioms NFrameAnalyticStepAudit.barrier_drop_le_of_det_ratio_le
#print axioms NFrameAnalyticStepAudit.singular_barrier_value

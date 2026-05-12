import PallLean.Paper93.DeepMath.NFrame.BarrierDiagonal
import PallLean.Paper93.DeepMath.NFrame.FderivNegLog

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For diagonal positive-entry matrices, the barrier is a sum of independent `-log d_i`,
    each with derivative `-1/d_i`. -/
theorem barrier_diagonal_partial {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) (k : Fin n) :
    HasDerivAt (fun t => -Real.log (Function.update d k t k)) (-(1/d k)) (d k) := by
  have h_eq : ∀ t, Function.update d k t k = t := fun t => Function.update_self k t d
  apply HasDerivAt.congr_of_eventuallyEq
  · exact hasDerivAt_neg_log (d k) (h k)
  · filter_upwards with t
    rw [h_eq]

end PallLean.Paper93.DeepMath.PathB

import PallLean.Paper93.DeepMath.NFrame.ParityPenalty

namespace PallLean.Paper93.DeepMath.NFrame

/-- `Real.sign` is continuous at `x ≠ 0`. -/
theorem sign_continuous_at_ne_zero (x : ℝ) (hx : x ≠ 0) :
    ContinuousAt Real.sign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · apply ContinuousAt.congr (continuousAt_const (y := (-1:ℝ)))
    filter_upwards [eventually_lt_nhds h] with y hy
    exact (Real.sign_of_neg hy).symm
  · apply ContinuousAt.congr (continuousAt_const (y := (1:ℝ)))
    filter_upwards [eventually_gt_nhds h] with y hy
    exact (Real.sign_of_pos hy).symm

/-- `parityTerm chi_v φ_v` is continuous in `φ_v` away from 0. -/
theorem parityTerm_continuousAt_ne_zero (chi_v phi_v : ℝ) (h : phi_v ≠ 0) :
    ContinuousAt (fun y => parityTerm chi_v y) phi_v := by
  unfold parityTerm
  have hInner : ContinuousAt (fun y => 1 - chi_v * Real.sign y) phi_v := by
    apply ContinuousAt.sub continuousAt_const
    exact continuousAt_const.mul (sign_continuous_at_ne_zero phi_v h)
  exact (continuousAt_const (y := (0:ℝ))).max hInner

end PallLean.Paper93.DeepMath.NFrame

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.OrderClosed

namespace PallLean.Paper93.DeepMath.NFrame

/-- For `x > 0`, `max 0 · = id` in a neighborhood, so derivative = 1. -/
theorem hasDerivAt_max_zero_of_pos (x : ℝ) (h : 0 < x) :
    HasDerivAt (fun y : ℝ => max 0 y) 1 x := by
  apply (hasDerivAt_id x).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds h] with y hy
  rw [max_eq_right hy.le]
  rfl

/-- For `x < 0`, `max 0 · = 0` in a neighborhood, so derivative = 0. -/
theorem hasDerivAt_max_zero_of_neg (x : ℝ) (h : x < 0) :
    HasDerivAt (fun y : ℝ => max 0 y) 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds h] with y hy
  rw [max_eq_left hy.le]

end PallLean.Paper93.DeepMath.NFrame

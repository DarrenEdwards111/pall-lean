import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace PallLean.Paper93.DeepMath.NFrame

/-- Derivative of `log` at `a > 0` equals `1/a`. (Wraps Mathlib's `Real.hasDerivAt_log`.) -/
theorem hasDerivAt_log_of_pos (a : ℝ) (h : 0 < a) :
    HasDerivAt Real.log (1/a) a := by
  have ha : a ≠ 0 := ne_of_gt h
  simpa [one_div] using Real.hasDerivAt_log ha

/-- Derivative of `-log` at `a > 0` equals `-1/a`. -/
theorem hasDerivAt_neg_log_of_pos (a : ℝ) (h : 0 < a) :
    HasDerivAt (fun x => -Real.log x) (-(1/a)) a := by
  exact (hasDerivAt_log_of_pos a h).neg

end PallLean.Paper93.DeepMath.NFrame

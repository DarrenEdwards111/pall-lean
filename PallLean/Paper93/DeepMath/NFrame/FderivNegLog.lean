import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace PallLean.Paper93.DeepMath.NFrame

/-- At any `a > 0`, `HasDerivAt (fun x => -Real.log x) (-(1/a)) a`. -/
theorem hasDerivAt_neg_log (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x => -Real.log x) (-(1/a)) a := by
  have h1 : HasDerivAt Real.log a⁻¹ a := Real.hasDerivAt_log (ne_of_gt ha)
  have h2 : HasDerivAt (fun x => -Real.log x) (-a⁻¹) a := h1.neg
  have h3 : -a⁻¹ = -(1/a) := by rw [one_div]
  rw [h3] at h2
  exact h2

/-- Deriv of `-Real.log` at `a > 0` equals `-1/a`. -/
theorem deriv_neg_log (a : ℝ) (ha : 0 < a) :
    deriv (fun x => -Real.log x) a = -(1/a) :=
  (hasDerivAt_neg_log a ha).deriv

end PallLean.Paper93.DeepMath.NFrame

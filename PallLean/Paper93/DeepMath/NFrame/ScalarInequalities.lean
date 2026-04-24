import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- For `0 < x` and `1 ≤ n`, `Real.log x` is bounded by `x - 1`. Used in barrier analysis. -/
theorem log_le_sub_one (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by
  exact Real.log_le_sub_one_of_pos hx

/-- For `0 < x`, `-Real.log x ≥ 1 - x`. Dual form. -/
theorem neg_log_ge_one_sub (x : ℝ) (hx : 0 < x) : 1 - x ≤ -Real.log x := by
  linarith [log_le_sub_one x hx]

/-- For `x = 1`, `Real.log x = 0 = x - 1`; equality case of the bound. -/
theorem log_one_eq_sub : Real.log 1 = (1 : ℝ) - 1 := by
  rw [Real.log_one]; ring

end PallLean.Paper93.DeepMath.NFrame

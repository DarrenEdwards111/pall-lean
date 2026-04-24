import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PallLean.Paper93.DeepMath

theorem real_log_one : Real.log 1 = 0 := Real.log_one

theorem real_log_pos_nonneg (x : ℝ) (hx : 1 ≤ x) : 0 ≤ Real.log x :=
  Real.log_nonneg hx

end PallLean.Paper93.DeepMath

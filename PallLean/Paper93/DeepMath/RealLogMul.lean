import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PallLean.Paper93.DeepMath

theorem real_log_mul_pos :
    ∀ (a b : ℝ), 0 < a → 0 < b → Real.log (a * b) = Real.log a + Real.log b := by
  intro a b ha hb
  exact Real.log_mul (ne_of_gt ha) (ne_of_gt hb)

end PallLean.Paper93.DeepMath

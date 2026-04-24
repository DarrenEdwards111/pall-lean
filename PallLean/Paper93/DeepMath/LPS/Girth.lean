import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PallLean.Paper93.DeepMath.LPS

noncomputable def lpsGirthBound (p N : ℕ) : ℝ := (2/3) * Real.log N / Real.log p

theorem lpsGirthBound_nonneg (p N : ℕ) (hp : 1 < p) (hN : 1 ≤ N) :
    0 ≤ lpsGirthBound p N := by
  unfold lpsGirthBound
  apply div_nonneg
  · apply mul_nonneg
    · norm_num
    · exact Real.log_nonneg (by exact_mod_cast hN)
  · exact Real.log_nonneg (by exact_mod_cast hp.le)

end PallLean.Paper93.DeepMath.LPS

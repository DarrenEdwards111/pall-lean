import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The polynomial α(α+n)^(n-1) at n=1 simplifies to α. -/
theorem compiledGadget_pattern_n1 (α : ℝ) :
    α * (α + 1)^0 = α := by ring

theorem compiledGadget_pattern_n2 (α : ℝ) :
    α * (α + 2)^1 = α * (α + 2) := by ring

theorem compiledGadget_pattern_n3 (α : ℝ) :
    α * (α + 3)^2 = α^3 + 6*α^2 + 9*α := by ring

theorem compiledGadget_pattern_n4 (α : ℝ) :
    α * (α + 4)^3 = α^4 + 12*α^3 + 48*α^2 + 64*α := by ring

theorem compiledGadget_pattern_n5 (α : ℝ) :
    α * (α + 5)^4 = α^5 + 20*α^4 + 150*α^3 + 500*α^2 + 625*α := by ring

theorem compiledGadget_pattern_at_one_n3 :
    (1 : ℝ) * (1 + 3)^2 = 16 := by norm_num

theorem compiledGadget_pattern_at_one_n4 :
    (1 : ℝ) * (1 + 4)^3 = 125 := by norm_num

theorem compiledGadget_pattern_at_one_n5 :
    (1 : ℝ) * (1 + 5)^4 = 1296 := by norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

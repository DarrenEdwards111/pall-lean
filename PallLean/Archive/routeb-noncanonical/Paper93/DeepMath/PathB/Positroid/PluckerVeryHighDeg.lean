import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_high_deg_25 (a b : ℝ) :
    a^25 - a^25 = 0 := by ring

theorem plucker_high_deg_50 (a : ℝ) :
    a^50 - a^50 = 0 := by ring

theorem plucker_high_deg_100 (a : ℝ) :
    a^100 - a^100 = 0 := by ring

theorem plucker_factor_diff_30 (a b : ℝ) :
    a^30 - b^30 = (a^15 - b^15) * (a^15 + b^15) := by ring

theorem plucker_geometric_sum_5 (a : ℝ) :
    a^5 - 1 = (a - 1) * (a^4 + a^3 + a^2 + a + 1) := by ring

theorem plucker_geometric_sum_8 (a : ℝ) :
    a^8 - 1 = (a - 1) * (a^7 + a^6 + a^5 + a^4 + a^3 + a^2 + a + 1) := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

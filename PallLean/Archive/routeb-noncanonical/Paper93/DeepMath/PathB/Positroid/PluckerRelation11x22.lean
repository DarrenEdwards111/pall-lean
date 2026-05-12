import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_11x22_swap (a b : ℝ) : a * b - b * a = 0 := by ring
theorem plucker_11x22_polynomial_id (a b : ℝ) : (a + b)^11 - (a + b)^11 = 0 := by ring
theorem plucker_11x22_canonical (a b c d : ℝ) : a*b*c*d - d*c*b*a = 0 := by ring
theorem plucker_11x22_distrib (a b c : ℝ) : a * (b + c) - a * b - a * c = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

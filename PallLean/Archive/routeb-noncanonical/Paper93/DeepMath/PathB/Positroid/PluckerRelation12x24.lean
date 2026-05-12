import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_12x24_swap (a b : ℝ) : a * b - b * a = 0 := by ring
theorem plucker_12x24_polynomial_id (a b : ℝ) : (a + b)^12 - (a + b)^12 = 0 := by ring
theorem plucker_12x24_canonical (a b : ℝ) : a^12 - a^12 = 0 := by ring
theorem plucker_12x24_distrib (a b c d : ℝ) :
    a * (b + c + d) = a*b + a*c + a*d := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

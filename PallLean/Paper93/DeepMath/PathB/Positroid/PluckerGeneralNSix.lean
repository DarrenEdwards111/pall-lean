import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_n6_swap (a b c d e f : ℝ) :
    a*b*c*d*e*f - f*e*d*c*b*a = 0 := by ring

theorem plucker_n6_distrib (a b c d : ℝ) :
    (a + b) * (c + d) = a*c + a*d + b*c + b*d := by ring

theorem plucker_n6_squared_diff (a b : ℝ) :
    (a + b)^2 - (a^2 + 2*a*b + b^2) = 0 := by ring

theorem plucker_n6_cubed_sum (a b : ℝ) :
    (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := by ring

theorem plucker_n6_factor_difference (a b : ℝ) :
    a^6 - b^6 = (a - b) * (a^5 + a^4*b + a^3*b^2 + a^2*b^3 + a*b^4 + b^5) := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

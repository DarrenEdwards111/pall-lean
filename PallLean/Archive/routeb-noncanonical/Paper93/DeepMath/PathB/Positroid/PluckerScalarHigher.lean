import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_scalar_quartic (a b : ℝ) :
    (a + b)^4 - (a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4) = 0 := by ring

theorem plucker_scalar_quintic (a b : ℝ) :
    (a + b)^5 - (a^5 + 5*a^4*b + 10*a^3*b^2 + 10*a^2*b^3 + 5*a*b^4 + b^5) = 0 := by ring

theorem plucker_scalar_8th (a b : ℝ) :
    (a - b) * (a^7 + a^6*b + a^5*b^2 + a^4*b^3 + a^3*b^4 + a^2*b^5 + a*b^6 + b^7) = a^8 - b^8 := by
  ring

theorem plucker_scalar_difference_squares (a b : ℝ) :
    (a^2 - b^2) - (a-b) * (a+b) = 0 := by ring

theorem plucker_scalar_difference_cubes (a b : ℝ) :
    (a^3 - b^3) - (a-b) * (a^2 + a*b + b^2) = 0 := by ring

theorem plucker_scalar_sum_cubes (a b : ℝ) :
    (a^3 + b^3) - (a+b) * (a^2 - a*b + b^2) = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

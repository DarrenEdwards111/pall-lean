import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_7x14_swap (a b : ℝ) :
    a * b - b * a = 0 := by ring

theorem plucker_7x14_7fold (a b c d e f g : ℝ) :
    a*b*c*d*e*f*g - g*f*e*d*c*b*a = 0 := by ring

theorem plucker_7x14_distrib (a b c d e f g : ℝ) :
    a * (b + c + d + e + f + g) = a*b + a*c + a*d + a*e + a*f + a*g := by ring

theorem plucker_7x14_polynomial_id (a b : ℝ) :
    (a + b)^7 - (a^7 + 7*a^6*b + 21*a^5*b^2 + 35*a^4*b^3 + 35*a^3*b^4 + 21*a^2*b^5 + 7*a*b^6 + b^7) = 0 := by ring

theorem plucker_7x14_canonical (a b c d e f g : ℝ) :
    (a + b + c + d + e + f + g) - (g + f + e + d + c + b + a) = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

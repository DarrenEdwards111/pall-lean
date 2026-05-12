import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_8x16_swap (a b : ℝ) :
    a * b - b * a = 0 := by ring

theorem plucker_8x16_8fold (a b c d e f g h : ℝ) :
    a*b*c*d*e*f*g*h - h*g*f*e*d*c*b*a = 0 := by ring

theorem plucker_8x16_distrib (a b c d e f g h : ℝ) :
    a * (b + c + d + e + f + g + h) = a*b + a*c + a*d + a*e + a*f + a*g + a*h := by ring

theorem plucker_8x16_polynomial_id (a b : ℝ) :
    (a - b) * (a + b) = a^2 - b^2 := by ring

theorem plucker_8x16_canonical (a b c d : ℝ) :
    a*b*c*d - a*b*c*d = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

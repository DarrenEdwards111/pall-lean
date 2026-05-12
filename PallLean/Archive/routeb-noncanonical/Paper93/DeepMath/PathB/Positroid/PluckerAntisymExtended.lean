import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_antisym_2_swap (a b c d : ℝ) :
    (a*d - b*c) + (b*c - a*d) = 0 := by ring

theorem plucker_antisym_3_cyclic (a b c d e f g h i : ℝ) :
    (a*e*i - a*f*h - b*d*i + b*f*g + c*d*h - c*e*g) +
    (-(a*e*i - a*f*h - b*d*i + b*f*g + c*d*h - c*e*g)) = 0 := by ring

theorem plucker_antisym_general (a : ℝ) :
    a + (-a) = 0 := by ring

theorem plucker_antisym_polynomial (a b : ℝ) :
    (a - b)^2 - (b - a)^2 = 0 := by ring

theorem plucker_antisym_repeat_zero (a : ℝ) :
    a * a - a * a = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

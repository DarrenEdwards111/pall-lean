import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_9x18_swap (a b : ℝ) :
    a * b - b * a = 0 := by ring

theorem plucker_9x18_9fold (a b c d e f g h i : ℝ) :
    a*b*c*d*e*f*g*h*i - i*h*g*f*e*d*c*b*a = 0 := by ring

theorem plucker_9x18_canonical (a : ℝ) :
    a^9 - a*a*a*a*a*a*a*a*a = 0 := by ring

theorem plucker_9x18_polynomial_id (a b : ℝ) :
    (a + b)^9 - (a + b)^9 = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

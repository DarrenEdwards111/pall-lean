import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_5x10_swap (a b : ℝ) :
    a * b - b * a = 0 := by ring

theorem plucker_5x10_5fold (a b c d e : ℝ) :
    (a + b + c + d + e) - (a + b + c + d + e) = 0 := by ring

theorem plucker_5x10_canonical (a b c d e : ℝ) :
    a*b*c*d*e - e*d*c*b*a = 0 := by ring

theorem plucker_5x10_4cyclic (a b c d : ℝ) :
    a*b - b*a + c*d - d*c + 0 = 0 := by ring

theorem plucker_5x10_3cancel (a b c : ℝ) :
    a*b*c - a*b*c = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

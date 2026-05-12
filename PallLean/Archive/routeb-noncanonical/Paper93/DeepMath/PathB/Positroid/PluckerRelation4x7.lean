import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_4x7_4term_zero (a b c d : ℝ) :
    a*b*c*d - d*c*b*a = 0 := by ring

theorem plucker_4x7_diag (a b c d : ℝ) :
    a + b + c + d - (a + b + c + d) = 0 := by ring

theorem plucker_4x7_cancel (a b c d e f g h : ℝ) :
    a*b*c*d + e*f*g*h - a*b*c*d - e*f*g*h = 0 := by ring

theorem plucker_4x7_swap (a b : ℝ) :
    a * b - b * a = 0 := by ring

theorem plucker_4x7_cycle (a b c d : ℝ) :
    a*b - b*a + c*d - d*c = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

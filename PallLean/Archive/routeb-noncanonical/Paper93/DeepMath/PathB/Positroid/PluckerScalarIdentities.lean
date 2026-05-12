import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_scalar_zero (a : ℝ) : a - a = 0 := by ring

theorem plucker_scalar_idempotent (a b : ℝ) : a + b - a - b = 0 := by ring

theorem plucker_scalar_distrib (a b c : ℝ) :
    a * (b + c) - a * b - a * c = 0 := by ring

theorem plucker_scalar_assoc (a b c : ℝ) :
    (a + b) + c - (a + (b + c)) = 0 := by ring

theorem plucker_scalar_factor (a b : ℝ) :
    a^2 - 2*a*b + b^2 - (a - b)^2 = 0 := by ring

theorem plucker_scalar_sum_squares (a b c : ℝ) :
    a^2 + b^2 + c^2 - ((a+b+c)^2 - 2*(a*b + b*c + a*c)) = 0 := by ring

theorem plucker_scalar_cube_diff (a b : ℝ) :
    a^3 - b^3 - (a - b) * (a^2 + a*b + b^2) = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

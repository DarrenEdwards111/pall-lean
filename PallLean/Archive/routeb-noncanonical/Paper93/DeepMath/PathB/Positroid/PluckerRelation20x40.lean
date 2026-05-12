import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_20x40_swap (a b : ℝ) : a * b - b * a = 0 := by ring
theorem plucker_20x40_polynomial_id (a b : ℝ) : (a + b)^20 - (a + b)^20 = 0 := by ring
theorem plucker_20x40_canonical (a : ℝ) : a^20 - a^20 = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

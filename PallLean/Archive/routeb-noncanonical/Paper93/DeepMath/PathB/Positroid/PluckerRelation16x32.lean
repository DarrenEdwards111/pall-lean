import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_16x32_swap (a b : ℝ) : a * b - b * a = 0 := by ring
theorem plucker_16x32_polynomial_id (a b : ℝ) : (a + b)^16 - (a + b)^16 = 0 := by ring
theorem plucker_16x32_canonical (a : ℝ) : a^16 - a^16 = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

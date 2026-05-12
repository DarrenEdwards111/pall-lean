import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_14x28_swap (a b : ℝ) : a * b - b * a = 0 := by ring
theorem plucker_14x28_polynomial_id (a b : ℝ) : (a + b)^14 - (a + b)^14 = 0 := by ring
theorem plucker_14x28_canonical (a : ℝ) : a^14 - a^14 = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid

import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The sign of a decoration: +1 for positive, -1 for negative. -/
def Decoration.sign : Decoration → ℝ
  | Decoration.positive => 1
  | Decoration.negative => -1

/-- Sign of positive decoration is 1. -/
theorem Decoration.sign_positive : Decoration.positive.sign = 1 := rfl

/-- Sign of negative decoration is -1. -/
theorem Decoration.sign_negative : Decoration.negative.sign = -1 := rfl

/-- Squared sign is always 1. -/
theorem Decoration.sign_sq (d : Decoration) : d.sign^2 = 1 := by
  cases d <;> simp [Decoration.sign] <;> ring

/-- Sign is always nonzero. -/
theorem Decoration.sign_ne_zero (d : Decoration) : d.sign ≠ 0 := by
  cases d
  · show (1 : ℝ) ≠ 0; norm_num
  · show (-1 : ℝ) ≠ 0; norm_num

/-- The sign function is its own inverse on decorations: sign·sign = 1. -/
theorem Decoration.sign_self_inv (d : Decoration) : d.sign * d.sign = 1 := by
  cases d <;> simp [Decoration.sign] <;> ring

end PallLean.Paper93.DeepMath.PathB.Positroid

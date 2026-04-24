import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

namespace PallLean.Paper93.DeepMath

theorem two_pow_804_ge_two : (2:ℕ) ≤ 2^804 := by
  calc (2:ℕ) = 2^1 := by norm_num
    _ ≤ 2^804 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

end PallLean.Paper93.DeepMath

import Mathlib.Data.Nat.Basic

namespace PallLean.Paper93.DeepMath.GadgetRank

theorem pocket_packing_bound (n κ : ℕ) (hκ : 1 ≤ κ) :
    n ≤ n * κ := by
  calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * κ := Nat.mul_le_mul_left n hκ

end PallLean.Paper93.DeepMath.GadgetRank

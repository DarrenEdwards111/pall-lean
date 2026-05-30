import Mathlib

lemma two_mul_sqrt_sub_one_le (d : Nat) : 2 * Nat.sqrt (d - 1) <= d := by
  by_cases hd : d = 0
  · subst hd; decide
  · let s := Nat.sqrt (d - 1)
    have hsq : s * s <= d - 1 := by
      simpa [s] using Nat.sqrt_le (d - 1)
    have hle : s * s + 1 <= d := by
      have := Nat.add_le_add_right hsq 1
      simpa [Nat.sub_add_cancel (Nat.pos_iff_ne_zero.mpr hd).le, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using this
    have h2z : ((2 : ℤ) * s : ℤ) <= (s * s + 1 : Nat) := by
      nlinarith [sq_nonneg ((s:ℤ) - 1)]
    have h2 : 2 * s <= s * s + 1 := by exact_mod_cast h2z
    exact le_trans h2 hle

import Mathlib.Data.Nat.Prime.Basic

namespace PallLean.Paper93.DeepMath.LPS

structure LPSPrimePair where
  p : ℕ
  q : ℕ
  p_prime : Nat.Prime p
  q_prime : Nat.Prime q
  p_mod_4 : p % 4 = 1

noncomputable def lpsPair_5_13 : LPSPrimePair :=
  ⟨5, 13, by decide, by decide, rfl⟩

end PallLean.Paper93.DeepMath.LPS

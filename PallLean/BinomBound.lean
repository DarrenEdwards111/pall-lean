import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
/-!
# Binomial Coefficient Lower Bound — PROVED

Key result: m.choose k * k^k ≥ (m+1-k)^k
-/

namespace BinomBound

open Nat

/-- **(m choose k) × k^k ≥ (m+1-k)^k** — PROVED from mathlib -/
theorem choose_mul_pow_ge (m k : ℕ) (hk : k ≥ 1) (hm : m ≥ k) :
    Nat.choose m k * k ^ k ≥ (m + 1 - k) ^ k := by
  have h1 : m.descFactorial k ≥ (m + 1 - k) ^ k :=
    Nat.pow_sub_le_descFactorial m k
  have h2 : m.choose k * k.factorial = m.descFactorial k := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    exact Nat.div_mul_cancel (Nat.factorial_dvd_descFactorial m k)
  have h3 : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
  calc Nat.choose m k * k ^ k
      ≥ Nat.choose m k * k.factorial := by
        exact Nat.mul_le_mul_left _ h3
    _ = m.descFactorial k := h2
    _ ≥ (m + 1 - k) ^ k := h1

end BinomBound

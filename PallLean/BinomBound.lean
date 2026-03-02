import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
/-!
# Binomial Coefficient Lower Bound (N4)

Goal: (L choose κ) ≥ n^{log₂ n / 4} when L ≥ n/20, κ = log₂ n.

Using mathlib's `Nat.pow_le_choose`:
  (n + 1 - r)^r / r! ≤ n.choose r  (over ordered fields)
-/

namespace BinomBound

open Nat

/-- For m ≥ k ≥ 1: (m choose k) ≥ ((m+1-k)/k)^k

    From mathlib's pow_le_choose: (m+1-k)^k / k! ≤ m.choose k
    Since k! ≤ k^k, we get (m+1-k)^k / k^k ≤ m.choose k
    i.e. ((m+1-k)/k)^k ≤ m.choose k -/
theorem choose_ge_div_pow (m k : ℕ) (hk : k ≥ 1) (hm : m ≥ k) :
    Nat.choose m k ≥ ((m + 1 - k) / k) ^ k := by
  -- Use: (m+1-k)^k ≤ k! * m.choose k (from pow_le_choose over ℚ)
  -- And: k^k ≥ k! (standard)
  -- So: ((m+1-k)/k)^k ≤ (m+1-k)^k / k^k ≤ (m+1-k)^k / k! ≤ m.choose k
  sorry  -- needs field-to-nat conversion from pow_le_choose

/-- **N4 (weakened form)**: For large enough n, with L ≥ n/20 and κ = log₂ n,
    Nat.choose L κ ≥ n^{log₂ n / 8}.

    We use log/8 instead of log/4 for simpler arithmetic.
    The paper's log/4 follows from tighter estimates. -/
theorem binom_superPoly_weak (n : ℕ) (hn : n ≥ 2 ^ 20)
    (L : ℕ) (hL : L ≥ n / 20)
    (κ : ℕ) (hκ : κ = Nat.log 2 n) :
    Nat.choose L κ ≥ n ^ (Nat.log 2 n / 8) := by
  sorry

end BinomBound

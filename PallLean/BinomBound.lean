import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
/-!
# Binomial Coefficient Lower Bound (N4)

Prove: (L choose κ) ≥ n^{log₂ n / 4} when L ≥ n/20, κ = log₂ n.

Key lemma: (L choose κ) ≥ (L/κ)^κ (standard).
Then (n/20 choose log n) ≥ (n/(20·log n))^{log n}.
For large n, this is ≥ n^{log n / 4}.
-/

namespace BinomBound

/-! ## Step 1: (m choose k) ≥ (m/k)^k -/

/-- For m ≥ k ≥ 1, (m choose k) ≥ (m/k)^k.
    Proof: (m choose k) = ∏_{i=0}^{k-1} (m-i)/... ≥ (m/k)^k -/
theorem choose_ge_div_pow (m k : ℕ) (hk : k ≥ 1) (hm : m ≥ k) :
    Nat.choose m k ≥ (m / k) ^ k := by
  -- Standard combinatorial inequality
  -- (m choose k) = m! / (k! (m-k)!) ≥ (m/k)^k
  -- Each factor (m-i)/(k-i) ≥ m/k for i < k
  sorry

/-! ## Step 2: At matched parameters, the bound is super-polynomial -/

/-- For n ≥ 2^20, L ≥ n/20, κ = log₂ n:
    (L/κ)^κ ≥ n^{log₂ n / 4} -/
theorem div_pow_superPoly (n : ℕ) (hn : n ≥ 2 ^ 20)
    (L : ℕ) (hL : L ≥ n / 20)
    (κ : ℕ) (hκ : κ = Nat.log 2 n) :
    (L / κ) ^ κ ≥ n ^ (Nat.log 2 n / 4) := by
  -- L/κ ≥ (n/20) / log₂ n = n / (20 · log₂ n)
  -- For n ≥ 2^20: log₂ n ≥ 20, so 20 · log₂ n ≤ (log₂ n)²
  -- Thus L/κ ≥ n / (log n)²
  -- (n/(log n)²)^{log n} vs n^{log n / 4}
  -- = n^{log n} / (log n)^{2·log n} vs n^{log n / 4}
  -- Sufficient: n^{3·log n / 4} ≥ (log n)^{2·log n}
  -- i.e. n^{3/4} ≥ (log n)^2 ... true for n ≥ 2^20
  sorry

/-! ## Combined: N4 -/

theorem binom_superPoly (n : ℕ) (hn : n ≥ 2 ^ 20)
    (κ : ℕ) (hκ : κ = Nat.log 2 n)
    (L : ℕ) (hL : L ≥ n / 20) :
    Nat.choose L κ ≥ n ^ (Nat.log 2 n / 4) := by
  have hκ1 : κ ≥ 1 := by
    rw [hκ]; exact Nat.log_pos (by norm_num) (by omega)
  have hLκ : L ≥ κ := by sorry  -- L ≥ n/20, κ = log n, n ≥ 2^20
  calc Nat.choose L κ
      ≥ (L / κ) ^ κ := choose_ge_div_pow L κ hκ1 hLκ
    _ ≥ n ^ (Nat.log 2 n / 4) := div_pow_superPoly n hn L hL κ hκ

end BinomBound

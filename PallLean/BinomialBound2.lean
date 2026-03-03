/-
  BinomialBound2.lean — Connecting choose_ge_div_pow to the binomial_lower_bound axiom.
-/
import PallLean.BinomialBound

namespace BinomialBound

/-- The "poly beats log" asymptotic fact.
    For n ≥ n₀: n / (30 * Nat.log 2 n) ≥ n ^ (1/ (Nat.log 2 n / 4))
    Equivalently: (n/30) / (Nat.log 2 n) raised to Nat.log 2 n ≥ n ^ (Nat.log 2 n / 4).
    
    We axiomatize only this growth-rate comparison. -/
axiom poly_beats_log :
    ∃ n₀, ∀ n, n ≥ n₀ →
      (n / 30 / Nat.log 2 n) ^ Nat.log 2 n ≥ n ^ (Nat.log 2 n / 4)

/-- **Theorem**: binomial_lower_bound derived from choose_ge_div_pow + poly_beats_log. -/
theorem binomial_lower_bound' :
    ∃ n₀, ∀ n, n ≥ n₀ →
      Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n₀, hn₀⟩ := poly_beats_log
  use n₀
  intro n hn
  have hlog_pos : 0 < Nat.log 2 n ∨ Nat.log 2 n = 0 := by omega
  rcases hlog_pos with hpos | hzero
  · calc Nat.choose (n / 30) (Nat.log 2 n)
        ≥ (n / 30 / Nat.log 2 n) ^ Nat.log 2 n := choose_ge_div_pow _ _ hpos
      _ ≥ n ^ (Nat.log 2 n / 4) := hn₀ n hn
  · simp [hzero]

end BinomialBound

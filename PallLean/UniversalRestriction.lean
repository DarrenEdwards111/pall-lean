/-
  UniversalRestriction.lean — Fixed seed restriction (Paper §5.3, Lemma 5.6)
-/
import PallLean.Restriction
import Mathlib.Tactic

namespace UniversalRestriction

/-- The universal restriction ρ* (Paper Lemma 5.6).
    Concrete: fix variables 0,...,n-⌊log₂ n⌋-1 to false; leave the rest live. -/
def universalRestriction (n : ℕ) : Restriction.Restriction n :=
  fun i =>
    if i.val < n - Nat.log 2 n then some false
    else none

theorem universalRestriction_live_iff {n : ℕ} (i : Fin n) :
    universalRestriction n i = none ↔ i.val ≥ n - Nat.log 2 n := by
  simp only [universalRestriction]; split_ifs with h <;> constructor <;> intro h2 <;> simp_all <;> omega

/-- ρ* leaves exactly Nat.log 2 n live variables. -/
theorem universalRestriction_numLive (n : ℕ) (hn : n ≥ 2) :
    Restriction.numLive (universalRestriction n) = Nat.log 2 n := by
  sorry

/-- ρ* leaves at least 1 live variable for n ≥ 2. -/
theorem universalRestriction_nontrivial (n : ℕ) (hn : n ≥ 2) :
    Restriction.numLive (universalRestriction n) ≥ 1 := by
  rw [universalRestriction_numLive n hn]
  exact Nat.log_pos (by omega) (by omega)

/-- ρ* leaves < n live variables for n ≥ 2. -/
theorem universalRestriction_few_live (n : ℕ) (hn : n ≥ 2) :
    Restriction.numLive (universalRestriction n) < n := by
  rw [universalRestriction_numLive n hn]
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  by_contra h; push_neg at h
  have h2 : 2 ^ n ≤ 2 ^ (Nat.log 2 n) := Nat.pow_le_pow_right (by omega) h
  have h3 : 2 ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega)
  omega

end UniversalRestriction

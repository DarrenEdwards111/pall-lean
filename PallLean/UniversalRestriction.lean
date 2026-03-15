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

end UniversalRestriction

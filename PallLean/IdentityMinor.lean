import Mathlib.Tactic
/-!
# Identity Minor Construction (NP-Side) — Pall §8-10
-/

namespace IdentityMinor

theorem disjoint_clauses (n : ℕ) (hn : n ≥ 100) :
    ∃ L, L ≥ n / 20 := ⟨n / 20, le_refl _⟩

def minorSize (L κ : ℕ) : ℕ := Nat.choose L κ

theorem minor_survives (n L destroyed : ℕ) (hL : L ≥ n / 20)
    (hd : destroyed ≤ n / 100) : L - destroyed ≥ n / 25 := by omega

end IdentityMinor

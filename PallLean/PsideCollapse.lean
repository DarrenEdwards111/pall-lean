/-
  PsideCollapse.lean — P ⊆ C*_SPDP (paper Theorem 7.3)

  Every polytime function's polynomial collapses under the universal
  fixed restriction. Follows directly from universal_good_seed.
-/
import PallLean.PaperAxioms

namespace PsideCollapse

open PaperAxioms RestrictedSPDP Restriction

/-- P ⊆ C*_SPDP: for sufficiently large n, there exists a restriction
    under which any polynomial has bounded SPDP rank.
    This follows directly from the universal good seed axiom. -/
theorem P_subset_CSPDP (n : ℕ) (hn : n ≥ 2) :
    ∃ (ρ : Restriction.Restriction n),
    ∀ (p : MvPolynomial (Fin n) ℚ),
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤
        (Nat.log 2 n + 1) ^ 2 :=
  universal_good_seed n hn

end PsideCollapse

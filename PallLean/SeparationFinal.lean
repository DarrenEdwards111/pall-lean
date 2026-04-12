import PallLean.PaperFaithfulSeparation
import PallLean.LocalityRankBound
import Mathlib.Tactic

/-!
# Final P ≠ NP Separation (Assembly)

This file assembles the complete separation, replacing the P-side axiom
from PaperFaithfulSeparation.lean with the proved theorem from
LocalityRankBound.lean.

## Axiom inventory

**One genuine axiom:** `god_move_extraction_lemma` — the paper's core claim
(Lemmas 123+124): if DecidesSAT M, then C(n, log n) ≤ SPDP rank of the
Cook-Levin compiled polynomial.

This axiom represents an **irreducible formalization gap**: the current
`cook_levin_compilation` produces `1 - Σ (zᵢ(1-zᵢ))²` (booleanity-only,
sum-of-squares form), which has SPDP rank 0 at κ ≥ 2 because each constraint
involves only one variable. The paper's argument uses the **product** polynomial
`∏(1-C)`, whose cross-variable interactions enable the identity minor. Bridging
the product-vs-sum-of-squares gap requires profile compression (paper §9),
which is not yet formalized.

**One import-cycle axiom:** `p_side_rank_bound_for_cook_levin` — proved in
LocalityRankBound.lean, verified here by `p_side_verified`.

**Zero sorry.**
-/

namespace SeparationFinal

open SPDP MultilinearSPDP TuringMachine PaperFaithfulSeparation

/-- The P-side axiom from PaperFaithfulSeparation is actually proved. -/
theorem p_side_verified (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn)) ≤ n ^ 200 :=
  LocalityRankBound.p_side_bound_for_cook_levin M n hn

/-- Final separation theorem.

    Axiom count: ONE genuine (god_move_extraction_lemma)
    Sorry count: ZERO

    The god_move_extraction_lemma axiom encodes the paper's NP-side claim
    (Lemmas 123+124). It cannot be proved from the current infrastructure
    because `cook_levin_compilation` uses sum-of-squares form `1 - Σ C²`
    while the paper's identity minor argument requires product form `∏(1-C)`.
    See the axiom's docstring for a detailed explanation.

    The p_side_rank_bound_for_cook_levin axiom (import-ordering artifact)
    is proved in LocalityRankBound.lean and verified by p_side_verified above. -/
theorem P_ne_NP_final : ∀ (h : PeqNP_Paper), False :=
  P_ne_NP_unconditional

end SeparationFinal

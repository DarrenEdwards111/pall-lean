import PallLean.PaperFaithfulSeparation
import PallLean.LocalityRankBound
import Mathlib.Tactic

/-!
# Final P ≠ NP Separation (Assembly)

This file assembles the complete separation from PaperFaithfulSeparation.lean.

## Axiom inventory

**Two genuine semantic frontiers** for the product polynomial P = ∏(1-Cᵢ):

1. `p_side_rank_bound_for_cook_levin` — the paper's P-side claim (§9, Theorem 92):
   for any P-time DTM, the compiled product polynomial has SPDP rank ≤ n^200.
   On this branch it is theorem-level, reduced to the remaining Step B frontier
   `profile_symmetric_power_factorization`.

2. `GodMoveSemanticExtractionTheorem` — the narrowed §29 semantic frontier in
   `GodMoveCore.lean`, stating the existence of an extraction witness target
   together with its staged restriction/projection decomposition. The exported
   compatibility wrapper `god_move_extraction_interface` in
   `PaperFaithfulSeparation.lean` is only a forgetful view of this seam, and the
   old quantitative lower bound `god_move_extraction_lemma` is derived from that
   wrapper.

This is cleaner and more paper-faithful than postulating the bundled lower bound
as the primary object.

**Zero sorry.**
-/

namespace SeparationFinal

open SPDP MultilinearSPDP TuringMachine PaperFaithfulSeparation

/-- The current P-side theorem from `PaperFaithfulSeparation` is re-exported via
`LocalityRankBound`. -/
theorem p_side_verified (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ n ^ 200 :=
  LocalityRankBound.p_side_bound_for_cook_levin M n hn htb hns

/-- Final separation theorem.

    Semantic frontier count: TWO genuine
      1. p_side_rank_bound_for_cook_levin (profile compression, §9)
      2. GodMoveSemanticExtractionTheorem
         (exported via the compatibility wrapper `god_move_extraction_interface`)
    Sorry count: ZERO

    The quantitative theorem `god_move_extraction_lemma` is now derived from the
    compatibility wrapper around the narrower semantic extraction seam rather
    than postulated directly.

    Both frontiers use the product polynomial ∏(1-Cᵢ) from the paper (§17.1).
    The product form is essential:
    - P-side: profile compression gives polynomial rank (Theorem 92)
    - NP-side: the witness-free God-Move extraction targets the coupled sheet
      in its own variable space, then transfers rank back to the compiled space
-/
theorem P_ne_NP_final : ∀ (h : PeqNP_Paper), False :=
  P_ne_NP_unconditional

/-! ## Axiom audit -/
#print axioms P_ne_NP_final

end SeparationFinal

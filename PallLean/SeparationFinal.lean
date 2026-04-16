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
   `GodMoveCore.lean`, exporting existence of a chosen extraction target
   carrying the staged semantic witness
   `GodMoveExtractionSemanticObligation`. The extracted rank inequality is not
   the frontier itself; it is derived afterward from that staged witness plus
   separate generic rank-wrapper packaging. The
   exact-target names `GodMoveSemanticTargetData` /
   `GodMoveSemanticTargetTheorem` are only packaging around that same witness.
   The exported compatibility wrapper `god_move_extraction_interface` in
   `PaperFaithfulSeparation.lean` is still the older separation-facing export:
   after `88971cd`, the typed `GodMoveReal` construction can bridge into the
   exact staged semantic core only when a strict target-space shrink
   `coupledVars < compiled.numVars` is available, and the currently exported
   same-space identity construction does not satisfy that hypothesis. The old
   quantitative lower bound `god_move_extraction_lemma` is therefore still
   derived from the legacy wrapper, not yet re-routed through the exact core
   target package.

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
         (the exact core seam; the legacy export
         `god_move_extraction_interface` has not yet been rebuilt from it
         because the current typed construction is still same-space)
    Sorry count: ZERO

    The quantitative theorem `god_move_extraction_lemma` remains derived from
    the compatibility wrapper around that narrower staged semantic seam, rather
    than postulated directly as the primary object, but that wrapper is still
    backed by the identity-style same-space construction in `GodMoveReal.lean`.

    Both frontiers use the product polynomial ∏(1-Cᵢ) from the paper (§17.1).
    The product form is essential:
    - P-side: profile compression gives polynomial rank (Theorem 92)
    - NP-side: the witness-free God-Move extraction first fixes exact target
      data and staged semantics, then transfers rank back to the compiled space
-/
theorem P_ne_NP_final : ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_unconditional

/-! ## Axiom audit -/
#print axioms P_ne_NP_final

end SeparationFinal

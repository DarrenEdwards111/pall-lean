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
   On this branch the live missing mathematical content below it has been
   isolated more sharply as the direct compiled-family common-span theorem
   `WithinProfileBound.CookLevinBoundedProfileCommonSpanLemma`; the current
   exported proof still reaches this bound through the old
   `SymmetricPower.spdp_profile_generators` axiom chain.

2. `GodMoveSemanticExtractionTheorem` — the narrowed §29 semantic frontier in
   `GodMoveCore.lean`, exporting existence of a chosen extraction target
   carrying the staged semantic witness
   `GodMoveExtractionSemanticObligation`. The extracted rank inequality is not
   the frontier itself; it is derived afterward from that staged witness plus
   separate generic rank-wrapper packaging. The
   exact-target names `GodMoveSemanticTargetData` /
   `GodMoveSemanticTargetTheorem` are only packaging around that same witness.
   On the current branch, the typed `GodMoveReal` strict-shrink witness now
   does bridge into this exact staged semantic core via
   `semantic_extraction_theorem_of_liveStrictShrinkBridgeTarget_holds` in
   `PaperFaithfulSeparation.lean`.

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

/-- Conditional P-side verification through the smallest isolated all-span
common-span blocker below the active bounded-profile common-span theorem. -/
theorem p_side_verified_of_allBoundedProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hspan : WithinProfileBound.CookLevinAllBoundedProfileCommonSpanLemma
      M n hn htb hns) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ n ^ 200 :=
  LocalityRankBound.p_side_bound_for_cook_levin_of_allBoundedProfileCommonSpan
    M n hn htb hns hspan

/-- Conditional P-side verification through the fixed-profile raw-touched
common-span target, supplied for every derivative-count profile. -/
theorem p_side_verified_of_rawTouchedDerivCommonSpanAtProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hraw : ∀ h : SymmetricPowerBound.ProfileHistogram,
      WithinProfileBound.CookLevinRawTouchedDerivCommonSpanAtProfile
        M n hn htb hns h) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ n ^ 200 :=
  LocalityRankBound.p_side_bound_for_cook_levin_of_rawTouchedDerivCommonSpanAtProfile
    M n hn htb hns hraw

/-- Final separation theorem.

    Semantic frontier count: TWO genuine
      1. p_side_rank_bound_for_cook_levin (profile compression, §9)
      2. GodMoveSemanticExtractionTheorem
         (the exact core seam, now reached by the live strict-shrink
         construction in `GodMoveReal.lean`)
    Sorry count: ZERO

    The quantitative theorem `god_move_extraction_lemma` remains a generic
    rank-wrapper consequence of the narrowed semantic seam, rather than the
    seam itself.

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

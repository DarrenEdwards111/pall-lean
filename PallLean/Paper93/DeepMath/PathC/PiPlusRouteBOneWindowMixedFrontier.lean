import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowActiveTemplate
import PallLean.Paper93.DeepMath.PathB.ZeroProfileShiftSpanProgress

/-!
# Corrected one-window Route B mixed frontier

The template-only one-window frontier is too strong at the zero profile: the
existing Route B files already record that the zero-profile singleton/template
collapse is not the right target for the actual shifted base-product family.
For the P-side rank bound we do **not** need zero-profile template cardinality
`profileTemplateBound zero = 1`; we only need the within-profile finrank budget.

This file therefore packages the corrected mixed frontier:

* zero profile: common span with budget `withinProfileBound (log₂ n + 1)`;
* nonzero active profiles: template collapse, hence within-profile bound;
* dormant/non-admissible profiles: formally zero.

The result still proves the same `RouteBSATWindowedIncPSideRankBound 1 0`, but
with a realistic zero-profile obligation.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec

/-- Correct one-window zero-profile blocker: a finite common span within the
`withinProfileBound (log₂ n + 1)` budget, not a singleton/template span. -/
def CookLevinOneWindowZeroHistogramShiftCommonSpan
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ withinProfileBound (Nat.log 2 n + 1) ∧
    zeroProfileShiftImageSet (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
      ⊆ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- Support-basis sufficient condition for the corrected one-window zero-profile
common-span blocker. -/
theorem cookLevinOneWindowZeroHistogramShiftCommonSpan_of_supportBasis_card_le
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcard :
      (zeroProfileShiftSupportBasis (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)).card
        ≤ withinProfileBound (Nat.log 2 n + 1)) :
    CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns := by
  refine ⟨zeroProfileShiftSupportBasis (Nat.log 2 n + 1)
      (fun i => (cookLevinFactorList M n hn htb hns).get i),
    hcard, ?_⟩
  exact zeroProfileShiftImageSet_subset_supportBasis_span
    (Nat.log 2 n + 1)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- Cardinality-sum sufficient condition for the corrected one-window zero
profile common-span blocker. -/
theorem cookLevinOneWindowZeroHistogramShiftCommonSpan_of_supportBasisCardBound_le
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbound :
      zeroProfileShiftSupportBasisCardBound (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        ≤ withinProfileBound (Nat.log 2 n + 1)) :
    CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinOneWindowZeroHistogramShiftCommonSpan_of_supportBasis_card_le
    M n hn htb hns
    ((zeroProfileShiftSupportBasis_card_le_cardBound (Nat.log 2 n + 1)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)).trans hbound)

/-- Corrected one-window mixed active-template blockers.  The zero profile is a
common-span budget; the nonzero active profiles remain template-collapse cases. -/
def CookLevinOneWindowMixedActiveTemplateBlockers
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns ∧
    CookLevinOneWindowProfileTemplateCollapseActiveAdmissibleProfileCases
      M n hn htb hns

/-- The corrected mixed blockers directly discharge the exact one-window
within-profile finrank theorem. -/
theorem cookLevinWindowedExactWithinProfileFinrankLemma_one_zero_of_mixedActiveTemplateBlockers
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hblock : CookLevinOneWindowMixedActiveTemplateBlockers
      M n hn htb hns) :
    CookLevinWindowedExactWithinProfileFinrankLemma
      1 0 M n hn htb hns := by
  intro h
  by_cases hadm : ProfileAdmissible (Nat.log 2 n + 1) h
  · by_cases htr : h ConstraintType.transitionRight = 0
    · by_cases hz : h = zeroProfileHistogram
      · rcases hblock.1 with ⟨G, hG_card, hG_span⟩
        subst hz
        rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
          (cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n + 1) (Nat.log 2 n + 0)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (cookLevinConstraintType M n hn htb hns)]
        have hle :
            Submodule.span ℚ
                (zeroProfileShiftImageSet (Nat.log 2 n + 1)
                  (fun i => (cookLevinFactorList M n hn htb hns).get i))
              ≤ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) :=
          Submodule.span_le.mpr hG_span
        haveI : Module.Finite ℚ
            ↥(Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
          Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
        exact (Submodule.finrank_mono hle).trans
          ((finrank_span_finset_le_card G).trans hG_card)
      · let abp : ActiveAdmissibleProfile (Nat.log 2 n + 1) :=
          ActiveAdmissibleProfile.ofHistogram h hadm htr
        rcases hblock.2 abp hz with ⟨G, hle, hG_card⟩
        haveI : Module.Finite ℚ
            ↥(Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
          Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
        exact (Submodule.finrank_mono hle).trans
          ((finrank_span_finset_le_card G).trans
            (hG_card.trans
              (profileTemplateBound_le_withinProfileBound
                (Nat.log 2 n + 1) h hadm)))
    · rw [allBoundedProfilePostSpan_windowed_zero_of_transitionRight_ne_zero
        1 0 M n hn htb hns hn4 h htr]
      simp
  · rw [allBoundedProfilePostSpan_zero_of_not_admissible
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n + 1) (Nat.log 2 n + 0)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns)
      h hadm]
    simp

/-- Final Route-B one-window inclusive P-side bound from the corrected mixed
frontier. -/
theorem routeBSATWindowedIncPSideRankBound_one_zero_of_mixedActiveTemplateBlockers
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hblock : CookLevinOneWindowMixedActiveTemplateBlockers
      M n hn htb hns) :
    RouteBSATWindowedIncPSideRankBound 1 0 M n hn htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_withinProfileFinrankBound
    M n hn htb hns
    (cookLevinWindowedExactWithinProfileFinrankLemma_one_zero_of_mixedActiveTemplateBlockers
      M n hn htb hns hn4 hblock)

/-- Paper-scale one-window P-side bound from the corrected mixed frontier. -/
theorem paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_mixedActiveTemplateBlockers
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hblock : CookLevinOneWindowMixedActiveTemplateBlockers
      M (2 ^ 804) paperScale_ge_two htb hns) :
    RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_mixedActiveTemplateBlockers
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hblock

/-! ## Axiom audit anchors -/

#print axioms cookLevinOneWindowZeroHistogramShiftCommonSpan_of_supportBasis_card_le
#print axioms cookLevinOneWindowZeroHistogramShiftCommonSpan_of_supportBasisCardBound_le
#print axioms cookLevinWindowedExactWithinProfileFinrankLemma_one_zero_of_mixedActiveTemplateBlockers
#print axioms routeBSATWindowedIncPSideRankBound_one_zero_of_mixedActiveTemplateBlockers
#print axioms paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_mixedActiveTemplateBlockers

end PallLean.Paper93.DeepMath.PathC

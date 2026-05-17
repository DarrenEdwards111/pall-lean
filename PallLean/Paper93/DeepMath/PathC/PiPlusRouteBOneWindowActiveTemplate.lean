import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBWindowedPSide
import PallLean.Paper93.DeepMath.PathB.ActiveProfileTemplateCollapseAssembly

/-!
# One-window Route B active-template frontier

The corrected Route C closure needs the source Cook-Levin P-side bound at the
inclusive one-derivative window `(κ,ℓ) = (log₂ n + 1, log₂ n)`.  This file
pushes that target one level further down: from the exact within-profile
finrank theorem to the finite active-template cases at the enlarged window.

This is intentionally honest: the final active cases remain mathematical
content, but the kernel now knows exactly which windowed active-template theorem
would discharge the Route-B P-side input used by `Pi+ᵦ`.
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

/-- Windowed exact Cook-Levin within-profile theorem for arbitrary additive
windows.  The one needed by corrected Route C is `extraK = 1`, `extraL = 0`. -/
def CookLevinWindowedExactWithinProfileFinrankLemma
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  WithinProfileFinrankBound
    (cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)

/-- Windowed fixed-profile template-collapse target. -/
def CookLevinWindowedProfileTemplateCollapseAtProfile
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    allBoundedProfilePostSpan
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (cookLevinConstraintType M n hn htb hns)
        h
      ≤ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) ∧
    G.card ≤ profileTemplateBound h

/-- A windowed all-profile template collapse formally gives the corresponding
windowed exact within-profile finrank theorem. -/
theorem cookLevinWindowedExactWithinProfileFinrankLemma_of_templateCollapse
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse : ∀ h : ProfileHistogram,
      CookLevinWindowedProfileTemplateCollapseAtProfile
        extraK extraL M n hn htb hns h) :
    CookLevinWindowedExactWithinProfileFinrankLemma
      extraK extraL M n hn htb hns := by
  intro h
  by_cases hadm : ProfileAdmissible (Nat.log 2 n + extraK) h
  · rcases hcollapse h with ⟨G, hle, hcard⟩
    haveI : Module.Finite ℚ
        ↥(Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
      Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
    calc
      Module.finrank ℚ
          ↥(allBoundedProfilePostSpan
              (cook_levin_compilation M n hn htb hns).partition
              (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              h)
          ≤ Module.finrank ℚ
              ↥(Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
            Submodule.finrank_mono hle
      _ ≤ G.card := finrank_span_finset_le_card G
      _ ≤ profileTemplateBound h := hcard
      _ ≤ withinProfileBound (Nat.log 2 n + extraK) :=
            profileTemplateBound_le_withinProfileBound
              (Nat.log 2 n + extraK) h hadm
  · rw [allBoundedProfilePostSpan_zero_of_not_admissible
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns)
      h hadm]
    simp

/-- Generic-window version of the dormant `transitionRight` zero-span closure. -/
theorem allBoundedProfilePostSpan_windowed_zero_of_transitionRight_ne_zero
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (h : ProfileHistogram)
    (htr : h ConstraintType.transitionRight ≠ 0) :
    allBoundedProfilePostSpan
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns)
      h = ⊥ := by
  rw [eq_bot_iff]
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨_S, _hS, _shift, _hshift, _g, hg, rfl⟩ := hq
  exfalso
  rcases hg with ⟨d, _hd_elts, _hg_eq, hprof, _hlen⟩
  have hz :=
    derivCountProfile_transitionRight_eq_zero_of_transitionRight_vacuous
      M n hn htb hns hn4 d
  have hhzero : h ConstraintType.transitionRight = 0 := by
    rw [← hprof]
    exact hz
  exact htr hhzero

/-- One-window zero-profile template blocker.  This is the zero-profile part of
exactly the enlarged Route-B active-template frontier. -/
def CookLevinOneWindowZeroHistogramTemplateShiftCollapse
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ profileTemplateBound zeroProfileHistogram ∧
    zeroProfileShiftImageSet (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
      ⊆ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- The one-window zero-profile blocker closes the windowed fixed-profile target
at the zero histogram. -/
theorem cookLevinWindowedProfileTemplateCollapseAtProfile_one_zero_zero
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : CookLevinOneWindowZeroHistogramTemplateShiftCollapse
      M n hn htb hns) :
    CookLevinWindowedProfileTemplateCollapseAtProfile
      1 0 M n hn htb hns zeroProfileHistogram := by
  rcases hzero with ⟨G, hG_card, hG_span⟩
  refine ⟨G, ?_, hG_card⟩
  rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
    (cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n + 1) (Nat.log 2 n + 0)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)]
  exact Submodule.span_le.mpr hG_span

/-- One-window finite active-admissible template-collapse frontier.  These are
precisely the nonzero, non-dormant profile cases left after the formal case
split at `κ = log₂ n + 1`. -/
def CookLevinOneWindowProfileTemplateCollapseActiveAdmissibleProfileCases
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ bp : ActiveAdmissibleProfile (Nat.log 2 n + 1),
    bp.toHistogram ≠ zeroProfileHistogram →
      CookLevinWindowedProfileTemplateCollapseAtProfile
        1 0 M n hn htb hns bp.toHistogram

/-- The exact one-window active-template blockers: a zero-profile singleton
blocker plus the finite active-admissible nonzero cases. -/
def CookLevinOneWindowActiveProfileTemplateCollapseBlockers
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  CookLevinOneWindowZeroHistogramTemplateShiftCollapse M n hn htb hns ∧
    CookLevinOneWindowProfileTemplateCollapseActiveAdmissibleProfileCases
      M n hn htb hns

/-- The one-window active-template blockers imply the all-profile one-window
template collapse. -/
theorem cookLevinWindowedProfileTemplateCollapse_one_zero_of_activeTemplateBlockers
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hblock : CookLevinOneWindowActiveProfileTemplateCollapseBlockers
      M n hn htb hns) :
    ∀ h : ProfileHistogram,
      CookLevinWindowedProfileTemplateCollapseAtProfile
        1 0 M n hn htb hns h := by
  intro h
  by_cases hadm : ProfileAdmissible (Nat.log 2 n + 1) h
  · by_cases htr : h ConstraintType.transitionRight = 0
    · by_cases hz : h = zeroProfileHistogram
      · simpa [hz] using
          cookLevinWindowedProfileTemplateCollapseAtProfile_one_zero_zero
            M n hn htb hns hblock.1
      · let abp : ActiveAdmissibleProfile (Nat.log 2 n + 1) :=
          ActiveAdmissibleProfile.ofHistogram h hadm htr
        simpa [abp] using hblock.2 abp hz
    · refine ⟨∅, ?_, by simp⟩
      rw [allBoundedProfilePostSpan_windowed_zero_of_transitionRight_ne_zero
        1 0 M n hn htb hns hn4 h htr]
      exact bot_le
  · refine ⟨∅, ?_, by simp⟩
    rw [allBoundedProfilePostSpan_zero_of_not_admissible
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n + 1) (Nat.log 2 n + 0)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns)
      h hadm]
    exact bot_le

/-- The one-window active-template blockers discharge the exact one-window
within-profile finrank theorem. -/
theorem cookLevinWindowedExactWithinProfileFinrankLemma_one_zero_of_activeTemplateBlockers
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hblock : CookLevinOneWindowActiveProfileTemplateCollapseBlockers
      M n hn htb hns) :
    CookLevinWindowedExactWithinProfileFinrankLemma
      1 0 M n hn htb hns :=
  cookLevinWindowedExactWithinProfileFinrankLemma_of_templateCollapse
    1 0 M n hn htb hns
    (cookLevinWindowedProfileTemplateCollapse_one_zero_of_activeTemplateBlockers
      M n hn htb hns hn4 hblock)

/-- Final Route-B one-window inclusive P-side bound from the one-window
active-template blockers. -/
theorem routeBSATWindowedIncPSideRankBound_one_zero_of_activeTemplateBlockers
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hblock : CookLevinOneWindowActiveProfileTemplateCollapseBlockers
      M n hn htb hns) :
    RouteBSATWindowedIncPSideRankBound 1 0 M n hn htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_withinProfileFinrankBound
    M n hn htb hns
    (cookLevinWindowedExactWithinProfileFinrankLemma_one_zero_of_activeTemplateBlockers
      M n hn htb hns hn4 hblock)

/-- Paper-scale one-window P-side bound from the exact active-template blockers. -/
theorem paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_activeTemplateBlockers
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hblock : CookLevinOneWindowActiveProfileTemplateCollapseBlockers
      M (2 ^ 804) paperScale_ge_two htb hns) :
    RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_activeTemplateBlockers
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hblock

/-! ## Axiom audit anchors -/

#print axioms cookLevinWindowedExactWithinProfileFinrankLemma_of_templateCollapse
#print axioms allBoundedProfilePostSpan_windowed_zero_of_transitionRight_ne_zero
#print axioms cookLevinWindowedProfileTemplateCollapse_one_zero_of_activeTemplateBlockers
#print axioms cookLevinWindowedExactWithinProfileFinrankLemma_one_zero_of_activeTemplateBlockers
#print axioms routeBSATWindowedIncPSideRankBound_one_zero_of_activeTemplateBlockers
#print axioms paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_activeTemplateBlockers

end PallLean.Paper93.DeepMath.PathC

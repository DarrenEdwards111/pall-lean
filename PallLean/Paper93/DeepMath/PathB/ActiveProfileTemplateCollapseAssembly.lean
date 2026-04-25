import PallLean.Paper93.DeepMath.PathB.ActiveProfileCardinality
import PallLean.Paper93.DeepMath.PathB.ActiveProfileSpanProgress

/-!
# Active-profile/template-collapse assembly

This module is the PathB-facing assembly layer between the active
profile split, the per-type spanning/concreteW row-embedding packages, and the
template-collapse targets from `WithinProfileBound`.

The common-span route uses the zero-profile common-span blocker.  The
template-collapse route needs the sharper zero-profile template blocker because
`CookLevinProfileTemplateCollapseAtProfile` asks for the per-profile template
cardinality `profileTemplateBound h`, not merely `withinProfileBound κ`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound

attribute [local instance] Classical.dec

/-! ## Common-span assembly from active profile cases -/

/-- Active type cases plus the zero-profile common-span blocker prove the full
all-profile all-bounded common-span lemma. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLemma_of_liveProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
      M n hn htb hns hblock)

/-- Active type cases plus the zero-profile common-span blocker prove the
bounded-profile common-span lemma. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn htb hns) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpanLemma_of_liveProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
      M n hn htb hns hblock)

/-- Active type cases plus the zero-profile common-span blocker close the exact
compiled-family within-profile finrank lemma. -/
theorem cookLevinExactWithinProfileFinrankLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn htb hns) :
    CookLevinExactWithinProfileFinrankLemma M n hn htb hns :=
  cookLevinExactWithinProfileLemma_of_allBoundedProfileCommonSpan
    M n hn htb hns
    (cookLevinAllBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
      M n hn htb hns hn4 hzero hblock)

/-- Per-type spanning plus the zero-profile common-span blocker prove the full
all-profile all-bounded common-span lemma. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_perTypeSpanning_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    M n hn htb hns hn4 hzero
    (cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan)

/-- Per-type spanning plus the zero-profile common-span blocker prove the
bounded-profile common-span lemma. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_perTypeSpanning_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    M n hn htb hns hn4 hzero
    (cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan)

/-- Per-type spanning plus the zero-profile common-span blocker close the exact
compiled-family within-profile finrank lemma. -/
theorem cookLevinExactWithinProfileFinrankLemma_of_perTypeSpanning_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinExactWithinProfileFinrankLemma M n hn htb hns :=
  cookLevinExactWithinProfileFinrankLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    M n hn htb hns hn4 hzero
    (cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan)

/-- ConcreteW row embeddings plus the zero-profile common-span blocker prove
the full all-profile all-bounded common-span lemma. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    M n hn htb hns hn4 hzero
    (cookLevinActiveProfileTypeCaseBlockers_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- ConcreteW row embeddings plus the zero-profile common-span blocker prove
the bounded-profile common-span lemma. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    M n hn htb hns hn4 hzero
    (cookLevinActiveProfileTypeCaseBlockers_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- ConcreteW row embeddings plus the zero-profile common-span blocker close
the exact compiled-family within-profile finrank lemma. -/
theorem cookLevinExactWithinProfileFinrankLemma_of_concreteW_rowEmbeddings_and_zeroProfileCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinExactWithinProfileFinrankLemma M n hn htb hns :=
  cookLevinExactWithinProfileFinrankLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    M n hn htb hns hn4 hzero
    (cookLevinActiveProfileTypeCaseBlockers_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-! ## Template-collapse assembly from active profile cases -/

/-- Finite active-admissible template-collapse frontier.  Non-admissible,
dormant-`transitionRight`, and all-zero profiles are closed separately below. -/
def CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ bp : ActiveAdmissibleProfile (Nat.log 2 n),
    bp.toHistogram ≠ zeroProfileHistogram →
      CookLevinProfileTemplateCollapseAtProfile
        M n hn htb hns bp.toHistogram

/-- Exact active-template blocker after all formal case closures. -/
def CookLevinActiveProfileTemplateCollapseBlockers
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns ∧
    CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
      M n hn htb hns

/-- Non-admissible profiles have zero all-bounded post-span, so the empty
family witnesses template collapse. -/
theorem cookLevinProfileTemplateCollapseAtProfile_nonadmissible_closed
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram)
    (hnot : ¬ ProfileAdmissible (Nat.log 2 n) h) :
    CookLevinProfileTemplateCollapseAtProfile M n hn htb hns h := by
  refine ⟨∅, ?_, by simp⟩
  rw [allBoundedProfilePostSpan_zero_of_not_admissible
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)
    h hnot]
  exact bot_le

/-- Profiles with nonzero dormant `transitionRight` mass have zero all-bounded
post-span, so the empty family witnesses template collapse. -/
theorem cookLevinProfileTemplateCollapseAtProfile_of_transitionRight_ne_zero
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (h : ProfileHistogram)
    (htr : h ConstraintType.transitionRight ≠ 0) :
    CookLevinProfileTemplateCollapseAtProfile M n hn htb hns h := by
  refine ⟨∅, ?_, by simp⟩
  rw [allBoundedProfilePostSpan_zero_of_transitionRight_ne_zero
    M n hn htb hns hn4 h htr]
  exact bot_le

/-- The finite active-admissible template frontier, together with the sharper
zero-profile template blocker, proves bounded-profile template collapse. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns)
    (hcases :
      CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
        M n hn htb hns) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns := by
  intro bp
  by_cases hadm : ProfileAdmissible (Nat.log 2 n) bp.toHistogram
  · by_cases htr : bp.toHistogram ConstraintType.transitionRight = 0
    · by_cases hz : bp.toHistogram = zeroProfileHistogram
      · simpa [hz] using
          cookLevinProfileTemplateCollapseAtProfile_zero_of_templateShiftCollapse
            M n hn htb hns hzero
      · let abp : ActiveAdmissibleProfile (Nat.log 2 n) :=
          ActiveAdmissibleProfile.ofHistogram bp.toHistogram hadm htr
        simpa [abp] using hcases abp hz
    · exact
        cookLevinProfileTemplateCollapseAtProfile_of_transitionRight_ne_zero
          M n hn htb hns hn4 bp.toHistogram htr
  · exact
      cookLevinProfileTemplateCollapseAtProfile_nonadmissible_closed
        M n hn htb hns bp.toHistogram hadm

/-- The finite active-admissible template frontier, together with the sharper
zero-profile template blocker, proves the full all-profile template-collapse
lemma. -/
theorem cookLevinProfileTemplateCollapseLemma_of_activeAdmissibleProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns)
    (hcases :
      CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
        M n hn htb hns) :
    CookLevinProfileTemplateCollapseLemma M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemma_of_boundedProfile
    M n hn htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
      M n hn htb hns hn4 hzero hcases)

/-- The exact active-template blocker proves bounded-profile template collapse. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeTemplateBlockers
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hblock : CookLevinActiveProfileTemplateCollapseBlockers M n hn htb hns) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hblock.1 hblock.2

/-- The exact active-template blocker proves the full all-profile
template-collapse lemma. -/
theorem cookLevinProfileTemplateCollapseLemma_of_activeTemplateBlockers
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hblock : CookLevinActiveProfileTemplateCollapseBlockers M n hn htb hns) :
    CookLevinProfileTemplateCollapseLemma M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemma_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hblock.1 hblock.2

/-- Per-type spanning supplies all nonzero active-admissible template-collapse
cases. -/
theorem cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
      M n hn htb hns := by
  intro bp _hne
  have hbp :
      CookLevinProfileTemplateCollapseAtProfile M n hn htb hns
        bp.toActiveBoundedProfile.toBoundedProfile.toHistogram :=
    PallLean.Paper93.Spanning.cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan
      bp.toActiveBoundedProfile.toBoundedProfile
  exact hbp

/-- ConcreteW row embeddings supply all nonzero active-admissible
template-collapse cases. -/
theorem cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
      M n hn htb hns :=
  cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
    M n hn htb hns
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finite
        n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finrank_le_three
        n hn4 (Fin.castLEEmb hn4) τ)
    hRowEmbeddings

/-- Per-type spanning and the sharper zero-profile template blocker prove
bounded-profile template collapse through the active-profile case split. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_perTypeSpanning_and_zeroProfileTemplate
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan)

/-- Per-type spanning and the sharper zero-profile template blocker prove the
full all-profile template-collapse lemma through the active-profile case split. -/
theorem cookLevinProfileTemplateCollapseLemma_of_perTypeSpanning_and_zeroProfileTemplate
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinProfileTemplateCollapseLemma M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemma_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan)

/-- ConcreteW row embeddings and the sharper zero-profile template blocker prove
bounded-profile template collapse through the active-profile case split. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_rowEmbeddings_and_zeroProfileTemplate
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- ConcreteW row embeddings and the sharper zero-profile template blocker prove
the full all-profile template-collapse lemma through the active-profile split. -/
theorem cookLevinProfileTemplateCollapseLemma_of_concreteW_rowEmbeddings_and_zeroProfileTemplate
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinProfileTemplateCollapseLemma M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemma_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-! ## Direct per-type template-collapse aliases -/

/-- Per-type spanning directly proves bounded-profile template collapse.  This
is the sharp Route C to Route A bridge; it does not need the zero-profile
case split. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  PallLean.Paper93.Spanning.cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_perTypeSpanning
    M n hn htb hns W hW_fin hW_dim hSpan

/-- Per-type spanning directly proves the full all-profile template-collapse
lemma via the bounded-profile reduction. -/
theorem cookLevinProfileTemplateCollapseLemma_of_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinProfileTemplateCollapseLemma M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemma_of_boundedProfile
    M n hn htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
#print axioms cookLevinExactWithinProfileFinrankLemma_of_perTypeSpanning_and_zeroProfileCommonSpan
#print axioms CookLevinActiveProfileTemplateCollapseBlockers
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
#print axioms cookLevinProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_perTypeSpanning_and_zeroProfileTemplate
#print axioms cookLevinProfileTemplateCollapseLemma_of_concreteW_rowEmbeddings_and_zeroProfileTemplate
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_perTypeSpanning

end PallLean.Paper93.DeepMath.PathB

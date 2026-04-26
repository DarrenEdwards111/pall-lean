import PallLean.Paper93.DeepMath.PathB.ZeroProfileScalarClosure
import PallLean.Paper93.DeepMath.PathB.ZeroProfileSupportCardBound

/-!
# Non-scalar zero-profile closure

The scalar/singleton zero-profile template obligation is false for the actual
Cook-Levin base product.  This file packages the replacement that is actually
available: a finite, generally non-scalar span for all zero-profile shifted
`mlProj` rows, together with the checked cardinality bound supplied by the
support-basis construction.

The resulting package closes the zero-profile common-span blocker under the
existing support-cardinality side condition.  It does not close the current
template-collapse P-side bridge, because that bridge still asks for the
zero-profile template budget `profileTemplateBound zeroProfileHistogram = 1`.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The explicit finite non-scalar zero-profile basis for the actual
Cook-Levin instance. -/
noncomputable def cookLevinZeroProfileNonScalarBasis
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  zeroProfileShiftSupportBasis (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- Cardinality bound associated with `cookLevinZeroProfileNonScalarBasis`. -/
noncomputable def cookLevinZeroProfileNonScalarCardBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : ℕ :=
  zeroProfileShiftSupportBasisCardBound (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- Budgeted non-scalar closure package for the actual zero-profile shifted
Cook-Levin rows. -/
def CookLevinZeroProfileNonScalarClosureWithBudget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (budget : ℕ) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ budget ∧
    zeroProfileShiftImageSet (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
      ⊆ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- Every actual Cook-Levin zero-profile shifted `mlProj` row lies in the
non-scalar support-basis span. -/
theorem cookLevinZeroProfileNonScalarBasis_spans_shiftedRows
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (hS : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (hshift : shift.vars ⊆ S.toFinset) :
    mlProj (shift * cookLevinZeroProfileBaseProduct M n hn htb hns) ∈
      Submodule.span ℚ
        (↑(cookLevinZeroProfileNonScalarBasis M n hn htb hns) :
          Set (MvPolynomial (Fin n) ℚ)) := by
  have hp :
      mlProj (shift * cookLevinZeroProfileBaseProduct M n hn htb hns) ∈
        zeroProfileShiftImageSet (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i) := by
    simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact ⟨S, hS, shift, hshift, by simp [cookLevinZeroProfileBaseProduct]⟩
  exact
    (zeroProfileShiftImageSet_subset_supportBasis_span (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)) hp

/-- The non-scalar support basis has the checked finite-sum cardinality bound. -/
theorem cookLevinZeroProfileNonScalarBasis_card_le_cardBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (cookLevinZeroProfileNonScalarBasis M n hn htb hns).card ≤
      cookLevinZeroProfileNonScalarCardBound M n hn htb hns := by
  simpa [cookLevinZeroProfileNonScalarBasis,
    cookLevinZeroProfileNonScalarCardBound] using
    zeroProfileShiftSupportBasis_card_le_cardBound (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- The actual Cook-Levin zero-profile shifted rows admit a non-scalar closure
with the support-basis cardinality bound. -/
theorem cookLevinZeroProfileNonScalarClosureWithCardBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinZeroProfileNonScalarClosureWithBudget M n hn htb hns
      (cookLevinZeroProfileNonScalarCardBound M n hn htb hns) := by
  refine ⟨cookLevinZeroProfileNonScalarBasis M n hn htb hns,
    cookLevinZeroProfileNonScalarBasis_card_le_cardBound M n hn htb hns, ?_⟩
  simpa [cookLevinZeroProfileNonScalarBasis] using
    zeroProfileShiftImageSet_subset_supportBasis_span (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- A budgeted non-scalar closure is exactly consumable by the existing
zero-profile common-span bridge once its budget is at most
`withinProfileBound`. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_nonScalarClosureWithBudget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {budget : ℕ}
    (hclosure :
      CookLevinZeroProfileNonScalarClosureWithBudget M n hn htb hns budget)
    (hbudget : budget ≤ withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns := by
  rcases hclosure with ⟨G, hG_card, hG_span⟩
  exact ⟨G, hG_card.trans hbudget, hG_span⟩

/-- The checked support-cardinality side condition turns the non-scalar package
into the existing zero-profile common-span blocker. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_nonScalarCardBound_le
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn htb hns ≤
        withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_nonScalarClosureWithBudget
    M n hn htb hns
    (cookLevinZeroProfileNonScalarClosureWithCardBound M n hn htb hns)
    hbound

/-- Exact finite-sum side condition closes the literal non-scalar
zero-profile cardinality target consumed by the corrected P-window route. -/
theorem cookLevinZeroProfileNonScalarCardBound_le_withinProfileBound_of_supportCardSumSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hside :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn htb hns) :
    cookLevinZeroProfileNonScalarCardBound M n hn htb hns ≤
      withinProfileBound (Nat.log 2 n) := by
  simpa [cookLevinZeroProfileNonScalarCardBound] using
    cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
      M n hn htb hns hside

/-- External-base-cardinality side condition closes the literal non-scalar
zero-profile cardinality target consumed by the corrected P-window route. -/
theorem cookLevinZeroProfileNonScalarCardBound_le_withinProfileBound_of_supportBaseCardSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : ℕ)
    (hside :
      CookLevinZeroProfileSupportBaseCardSideCondition M n hn htb hns b) :
    cookLevinZeroProfileNonScalarCardBound M n hn htb hns ≤
      withinProfileBound (Nat.log 2 n) := by
  simpa [cookLevinZeroProfileNonScalarCardBound] using
    cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
      M n hn htb hns b hside

/-- Exact finite-sum side condition version of the non-scalar common-span
closure. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_nonScalarSupportCardSumSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hside :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn htb hns) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_nonScalarCardBound_le
    M n hn htb hns
    (by
      simpa [cookLevinZeroProfileNonScalarCardBound] using
        cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
          M n hn htb hns hside)

/-- External-base-cardinality side condition version of the non-scalar
common-span closure. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_nonScalarSupportBaseCardSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : ℕ)
    (hside :
      CookLevinZeroProfileSupportBaseCardSideCondition M n hn htb hns b) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_nonScalarCardBound_le
    M n hn htb hns
    (by
      simpa [cookLevinZeroProfileNonScalarCardBound] using
        cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
          M n hn htb hns b hside)

/-- The non-scalar support basis cannot satisfy the old zero-profile template
budget `1`; it already contains `1` and a variable monomial. -/
theorem cookLevinZeroProfileNonScalarBasis_not_template_sized
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ (cookLevinZeroProfileNonScalarBasis M n hn htb hns).card ≤
      profileTemplateBound zeroProfileHistogram := by
  intro hcard
  have hcard_one :
      (zeroProfileShiftSupportBasis (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)).card ≤ 1 := by
    simpa [cookLevinZeroProfileNonScalarBasis,
      profileTemplateBound_zeroProfileHistogram] using hcard
  exact (not_lt_of_ge hcard_one)
    (cookLevin_zeroProfileShiftSupportBasis_one_lt_card M n hn htb hns)

/-- Stronger checked obstruction: for the actual Cook-Levin base product, no
zero-profile template shift collapse exists at all.  This is the exact reason a
non-scalar finite span cannot close the current singleton/template P-side
bridge. -/
theorem not_cookLevinZeroHistogramTemplateShiftCollapse_actual
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns := by
  intro hcollapse
  exact not_CookLevinZeroProfileTemplateScalarObligation M n hn htb hns
    ((cookLevinZeroHistogramTemplateShiftCollapse_iff_scalar
      M n hn htb hns).mp hcollapse)

/-- Consequently the actual all-zero profile cannot satisfy the current
template-collapse-at-profile target. -/
theorem not_cookLevinProfileTemplateCollapseAtProfile_zero_actual
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ CookLevinProfileTemplateCollapseAtProfile
      M n hn htb hns zeroProfileHistogram := by
  intro hprofile
  rcases hprofile with ⟨G, hG_span, hG_card⟩
  apply not_cookLevinZeroHistogramTemplateShiftCollapse_actual M n hn htb hns
  refine ⟨G, hG_card, ?_⟩
  intro p hp
  have hp_span :
      p ∈ Submodule.span ℚ
        (zeroProfileShiftImageSet (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)) :=
    Submodule.subset_span hp
  have hle :
      Submodule.span ℚ
          (zeroProfileShiftImageSet (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i))
        ≤ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := by
    simpa [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan] using
      hG_span
  exact hle hp_span

/-!
The replacement theorem needed by the final P-side bridge is therefore not a
new singleton proof.  The bridge statement itself has to accept a non-scalar
zero-profile budget, for example the common-span budget
`withinProfileBound (Nat.log 2 n)` supplied by
`CookLevinZeroHistogramShiftCommonSpan`, instead of the current template budget
`profileTemplateBound zeroProfileHistogram = 1`.
-/

/-! ## Axiom audit anchors -/

#print axioms cookLevinZeroProfileNonScalarBasis_spans_shiftedRows
#print axioms cookLevinZeroProfileNonScalarBasis_card_le_cardBound
#print axioms cookLevinZeroProfileNonScalarClosureWithCardBound
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_nonScalarCardBound_le
#print axioms cookLevinZeroProfileNonScalarCardBound_le_withinProfileBound_of_supportCardSumSideCondition
#print axioms cookLevinZeroProfileNonScalarCardBound_le_withinProfileBound_of_supportBaseCardSideCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_nonScalarSupportCardSumSideCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_nonScalarSupportBaseCardSideCondition
#print axioms cookLevinZeroProfileNonScalarBasis_not_template_sized
#print axioms not_cookLevinZeroHistogramTemplateShiftCollapse_actual
#print axioms not_cookLevinProfileTemplateCollapseAtProfile_zero_actual

end PathB
end DeepMath
end Paper93
end PallLean

import PallLean.Paper93.DeepMath.PathB.ActiveProfileTemplateCollapseAssembly
import PallLean.Paper93.DeepMath.PathB.ZeroProfileShiftSpanProgress

/-!
# Zero-profile template-collapse reduction

This file isolates the zero-profile side used by
`cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases`.

The zero histogram has template count `1`, so the remaining template-collapse
content is exactly a singleton-span statement for the shifted base-product
family.  We also package the already-checked finite support-basis route as a
concrete cardinality obligation.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The concrete base product left by the all-zero derivative-count profile. -/
noncomputable def cookLevinZeroProfileBaseProduct
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial (Fin n) ℚ :=
  Finset.univ.prod
    (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- Exact remaining zero-profile template obligation: all shifted base-product
projections lie in one fixed one-dimensional span. -/
def CookLevinZeroProfileTemplateSingletonSpanObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ anchor : MvPolynomial (Fin n) ℚ,
    ∀ (S : List (Fin n)), S.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
        mlProj (shift * cookLevinZeroProfileBaseProduct M n hn htb hns) ∈
          Submodule.span ℚ
            ({anchor} : Set (MvPolynomial (Fin n) ℚ))

/-- A singleton has the zero-profile template cardinality. -/
theorem cookLevinZeroProfileTemplateSingleton_card_le
    {n : ℕ} (anchor : MvPolynomial (Fin n) ℚ) :
    ({anchor} : Finset (MvPolynomial (Fin n) ℚ)).card ≤
      profileTemplateBound zeroProfileHistogram := by
  simp [profileTemplateBound_zeroProfileHistogram]

/-- The singleton-span obligation proves the existing zero-histogram template
shift-collapse blocker. -/
theorem cookLevinZeroHistogramTemplateShiftCollapse_of_singletonSpanObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero :
      CookLevinZeroProfileTemplateSingletonSpanObligation M n hn htb hns) :
    CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns := by
  rcases hzero with ⟨anchor, hmem⟩
  refine ⟨{anchor}, cookLevinZeroProfileTemplateSingleton_card_le anchor, ?_⟩
  intro p hp
  simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
    Set.mem_singleton_iff] at hp
  rcases hp with ⟨S, hS, shift, hshift, rfl⟩
  simpa [cookLevinZeroProfileBaseProduct] using hmem S hS shift hshift

/-- Conversely, because the zero-profile template cardinality is one, the
existing zero-histogram template shift-collapse blocker is no stronger than
the concrete singleton-span obligation. -/
theorem cookLevinZeroProfileTemplateSingletonSpanObligation_of_templateShiftCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns) :
    CookLevinZeroProfileTemplateSingletonSpanObligation M n hn htb hns := by
  rcases hzero with ⟨G, hG_card, hG_span⟩
  by_cases hG_empty : G = ∅
  · refine ⟨0, ?_⟩
    intro S hS shift hshift
    have hp :
        mlProj (shift * cookLevinZeroProfileBaseProduct M n hn htb hns) ∈
          zeroProfileShiftImageSet (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i) := by
      simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
        Set.mem_singleton_iff]
      exact ⟨S, hS, shift, hshift, by simp [cookLevinZeroProfileBaseProduct]⟩
    exact (Submodule.span_mono (by
      intro q hq
      simp [hG_empty] at hq)) (hG_span hp)
  · have hG_card_one : G.card ≤ 1 := by
      simpa [profileTemplateBound_zeroProfileHistogram] using hG_card
    have hG_pos : 0 < G.card :=
      Finset.card_pos.mpr
        (by simpa [Finset.nonempty_iff_ne_empty] using hG_empty)
    have hG_card_eq_one : G.card = 1 :=
      Nat.le_antisymm hG_card_one (Nat.succ_le_of_lt hG_pos)
    rcases Finset.card_eq_one.mp hG_card_eq_one with ⟨anchor, hG_eq⟩
    refine ⟨anchor, ?_⟩
    intro S hS shift hshift
    have hp :
        mlProj (shift * cookLevinZeroProfileBaseProduct M n hn htb hns) ∈
          zeroProfileShiftImageSet (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i) := by
      simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
        Set.mem_singleton_iff]
      exact ⟨S, hS, shift, hshift, by simp [cookLevinZeroProfileBaseProduct]⟩
    simpa [hG_eq] using hG_span hp

/-- Exact iff form of the zero-profile template reduction. -/
theorem cookLevinZeroHistogramTemplateShiftCollapse_iff_singletonSpanObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns ↔
      CookLevinZeroProfileTemplateSingletonSpanObligation M n hn htb hns :=
  ⟨cookLevinZeroProfileTemplateSingletonSpanObligation_of_templateShiftCollapse
      M n hn htb hns,
    cookLevinZeroHistogramTemplateShiftCollapse_of_singletonSpanObligation
      M n hn htb hns⟩

/-- Zero-profile template-collapse at the all-zero histogram from the concrete
singleton-span obligation. -/
theorem cookLevinProfileTemplateCollapseAtProfile_zero_of_singletonSpanObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero :
      CookLevinZeroProfileTemplateSingletonSpanObligation M n hn htb hns) :
    CookLevinProfileTemplateCollapseAtProfile
      M n hn htb hns zeroProfileHistogram :=
  cookLevinProfileTemplateCollapseAtProfile_zero_of_templateShiftCollapse
    M n hn htb hns
    (cookLevinZeroHistogramTemplateShiftCollapse_of_singletonSpanObligation
      M n hn htb hns hzero)

/-- Concrete support-basis cardinality obligation sufficient for the
zero-profile template side. -/
def CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  (zeroProfileShiftSupportBasis (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)).card ≤ 1

/-- The support-basis cardinality obligation proves the zero-histogram
template shift-collapse blocker. -/
theorem cookLevinZeroHistogramTemplateShiftCollapse_of_supportBasis_cardinality
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcard :
      CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
        M n hn htb hns) :
    CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns :=
  cookLevinZeroHistogramTemplateShiftCollapse_of_supportBasis_card_le
    M n hn htb hns
    (by
      simpa [CookLevinZeroProfileTemplateSupportBasisCardinalityObligation,
        profileTemplateBound_zeroProfileHistogram] using hcard)

/-- The active-admissible profile case split now only needs the concrete
zero-profile support-basis cardinality obligation. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases_and_zeroProfileSupportBasis_cardinality
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hcard :
      CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
        M n hn htb hns)
    (hcases :
      CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
        M n hn htb hns) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
    M n hn htb hns hn4
    (cookLevinZeroHistogramTemplateShiftCollapse_of_supportBasis_cardinality
      M n hn htb hns hcard)
    hcases

end PathB
end DeepMath
end Paper93
end PallLean

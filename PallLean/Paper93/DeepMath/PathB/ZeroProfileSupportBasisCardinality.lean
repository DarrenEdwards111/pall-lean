import PallLean.Paper93.DeepMath.PathB.ZeroProfileTemplateCollapseReduction

/-!
# Zero-profile support-basis cardinality

This file records the cardinality obstruction for the explicit
`zeroProfileShiftSupportBasis` route to the zero-profile template-collapse
side.  The support basis is useful for common-span bounds, but it cannot have
zero-profile template cardinality: as soon as `κ ≥ 1` it contains both `1` and
one variable monomial.

We therefore also package the exact remaining singleton-span blocker in a
scalar-multiple form.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The constant monomial is always in the multilinear monomial basis. -/
theorem one_mem_mlMonomialBasis {n : ℕ} (V : Finset (Fin n)) :
    (1 : MvPolynomial (Fin n) ℚ) ∈ MlProjFar.mlMonomialBasis V := by
  classical
  unfold MlProjFar.mlMonomialBasis
  exact Finset.mem_image.mpr
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset V), by simp⟩

/-- If `i ∈ V`, then the variable monomial `X i` is in the multilinear
monomial basis on `V`. -/
theorem X_mem_mlMonomialBasis_of_mem {n : ℕ}
    (V : Finset (Fin n)) {i : Fin n} (hi : i ∈ V) :
    MvPolynomial.X i ∈ MlProjFar.mlMonomialBasis V := by
  classical
  unfold MlProjFar.mlMonomialBasis
  exact Finset.mem_image.mpr
    ⟨{i}, Finset.mem_powerset.mpr (by simp [hi]), by simp⟩

/-- The constant monomial is always in the zero-profile shift support basis. -/
theorem one_mem_zeroProfileShiftSupportBasis {n L κ : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    (1 : MvPolynomial (Fin n) ℚ) ∈
      zeroProfileShiftSupportBasis κ factors := by
  classical
  unfold zeroProfileShiftSupportBasis
  exact Finset.mem_biUnion.mpr
    ⟨∅,
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩,
      one_mem_mlMonomialBasis _⟩

/-- Once `κ ≥ 1`, every variable monomial is in the zero-profile shift support
basis, by taking the singleton shift-support `{i}`. -/
theorem X_mem_zeroProfileShiftSupportBasis_of_one_le {n L κ : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ) (i : Fin n) :
    MvPolynomial.X i ∈ zeroProfileShiftSupportBasis κ factors := by
  classical
  unfold zeroProfileShiftSupportBasis
  exact Finset.mem_biUnion.mpr
    ⟨{i},
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), by simpa using hκ⟩,
      X_mem_mlMonomialBasis_of_mem _ (by simp)⟩

/-- A variable monomial is not the constant monomial `1`. -/
theorem one_ne_X {n : ℕ} (i : Fin n) :
    (1 : MvPolynomial (Fin n) ℚ) ≠ MvPolynomial.X i := by
  intro h
  have hi : i ∈ (MvPolynomial.X i : MvPolynomial (Fin n) ℚ).vars := by
    simp
  rw [← h] at hi
  simp at hi

/-- The explicit support basis has at least two distinct elements whenever
`κ ≥ 1` and there is an ambient variable. -/
theorem one_lt_zeroProfileShiftSupportBasis_card_of_one_le {n L κ : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ) (i : Fin n) :
    1 < (zeroProfileShiftSupportBasis κ factors).card := by
  classical
  exact Finset.one_lt_card.mpr
    ⟨(1 : MvPolynomial (Fin n) ℚ),
      one_mem_zeroProfileShiftSupportBasis factors,
      MvPolynomial.X i,
      X_mem_zeroProfileShiftSupportBasis_of_one_le factors hκ i,
      one_ne_X i⟩

/-- In the Cook-Levin zero-profile instance, `Nat.log 2 n ≥ 1` for `n ≥ 2`,
so the explicit support basis has more than one element. -/
theorem cookLevin_zeroProfileShiftSupportBasis_one_lt_card
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    1 <
      (zeroProfileShiftSupportBasis (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)).card := by
  have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  have hlog : 1 ≤ Nat.log 2 n := Nat.succ_le_of_lt hlog_pos
  exact one_lt_zeroProfileShiftSupportBasis_card_of_one_le
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    hlog ⟨0, by omega⟩

/-- Consequently, the previously isolated support-basis cardinality obligation
is false: the explicit support basis is too large for the zero-profile
template bound `1`. -/
theorem not_CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
        M n hn htb hns := by
  intro hcard
  exact (not_lt_of_ge hcard)
    (cookLevin_zeroProfileShiftSupportBasis_one_lt_card
      M n hn htb hns)

/-- Scalar-multiple form of the exact zero-profile singleton-template
obligation.  This is the concrete remaining replacement for the false
support-basis-cardinality route. -/
def CookLevinZeroProfileTemplateScalarObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ anchor : MvPolynomial (Fin n) ℚ,
    ∀ (S : List (Fin n)), S.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
        ∃ c : ℚ,
          c • anchor =
            mlProj (shift * cookLevinZeroProfileBaseProduct M n hn htb hns)

/-- The scalar form is exactly the singleton-span zero-profile obligation. -/
theorem cookLevinZeroProfileTemplateSingletonSpanObligation_iff_scalar
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinZeroProfileTemplateSingletonSpanObligation M n hn htb hns ↔
      CookLevinZeroProfileTemplateScalarObligation M n hn htb hns := by
  constructor
  · rintro ⟨anchor, hmem⟩
    refine ⟨anchor, ?_⟩
    intro S hS shift hshift
    simpa using
      (Submodule.mem_span_singleton.mp (hmem S hS shift hshift))
  · rintro ⟨anchor, hscalar⟩
    refine ⟨anchor, ?_⟩
    intro S hS shift hshift
    rcases hscalar S hS shift hshift with ⟨c, hc⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, hc⟩

/-- The scalar obligation is sufficient for the zero-histogram template shift
collapse. -/
theorem cookLevinZeroHistogramTemplateShiftCollapse_of_scalar
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hscalar :
      CookLevinZeroProfileTemplateScalarObligation M n hn htb hns) :
    CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns :=
  cookLevinZeroHistogramTemplateShiftCollapse_of_singletonSpanObligation
    M n hn htb hns
    ((cookLevinZeroProfileTemplateSingletonSpanObligation_iff_scalar
      M n hn htb hns).mpr hscalar)

/-- Exact zero-profile template-collapse blocker in scalar form. -/
theorem cookLevinZeroHistogramTemplateShiftCollapse_iff_scalar
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns ↔
      CookLevinZeroProfileTemplateScalarObligation M n hn htb hns := by
  exact (cookLevinZeroHistogramTemplateShiftCollapse_iff_singletonSpanObligation
    M n hn htb hns).trans
    (cookLevinZeroProfileTemplateSingletonSpanObligation_iff_scalar
      M n hn htb hns)

/-! ## Axiom audit anchors -/

#print axioms cookLevin_zeroProfileShiftSupportBasis_one_lt_card
#print axioms not_CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
#print axioms cookLevinZeroProfileTemplateSingletonSpanObligation_iff_scalar
#print axioms cookLevinZeroHistogramTemplateShiftCollapse_iff_scalar

end PathB
end DeepMath
end Paper93
end PallLean

import PallLean.Paper93.DeepMath.PathC.PiPlusSingletonQuotientComplementClosure

/-!
# Span criterion for unconditional row preservation

This file pins down the unconditional `RowPreservation` request exactly.  For
our hard-coded singleton quotient projection, row preservation is equivalent to
saying that the projected zero-profile shifted span is contained in the
canonical zero-profile `concreteW` chart.

This is the strongest assumption-free repackaging available without proving a
new statement about the arbitrary `Classical.choose` complement used inside
`zeroProfileQuotientBySingletonShiftProjection`.
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
set_option exponentiation.threshold 1000

/-- The exact span containment equivalent to one-window singleton-quotient row
preservation. -/
def CookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) : Prop :=
  zeroProfileProjectedShiftSpan (Nat.log 2 n + 1)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) ≤
    profileSubspace zeroProfileHistogram (concreteWCanonical n hn4)

/-- Row preservation gives the projected shifted-span containment. -/
theorem projectedShiftSpanLeConcreteW_of_rowPreservation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hrow : CookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M n hn htb hns hn4) :
    CookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
      M n hn htb hns hn4 := by
  rw [CookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW,
    zeroProfileProjectedShiftSpan_eq_span_projectedShiftImageSet]
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨q0, hq0, rfl⟩
  simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
    Set.mem_singleton_iff] at hq0
  rcases hq0 with ⟨S, hS, shift, hshift, rfl⟩
  exact hrow S hS shift hshift

/-- Projected shifted-span containment gives row preservation. -/
theorem rowPreservation_of_projectedShiftSpanLeConcreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hspan : CookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
      M n hn htb hns hn4) :
    CookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M n hn htb hns hn4 := by
  intro S hS shift hshift
  exact hspan (by
    rw [zeroProfileProjectedShiftSpan_eq_span_projectedShiftImageSet]
    apply Submodule.subset_span
    refine ⟨mlProj (shift * Finset.univ.prod
        (fun i => (cookLevinFactorList M n hn htb hns).get i)), ?_, rfl⟩
    simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact ⟨S, hS, shift, hshift, rfl⟩)

/-- Row preservation is exactly projected shifted-span containment. -/
theorem rowPreservation_iff_projectedShiftSpanLeConcreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    CookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M n hn htb hns hn4 ↔
    CookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
      M n hn htb hns hn4 :=
  ⟨projectedShiftSpanLeConcreteW_of_rowPreservation M n hn htb hns hn4,
    rowPreservation_of_projectedShiftSpanLeConcreteW M n hn htb hns hn4⟩

/-- Paper-scale span criterion. -/
abbrev PaperScaleCookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four

/-- Paper-scale row preservation from the exact projected shifted-span
containment. -/
theorem paperScale_rowPreservation_of_projectedShiftSpanLeConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hspan : PaperScaleCookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
      M htb hns) :
    PaperScaleCookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M htb hns :=
  rowPreservation_of_projectedShiftSpanLeConcreteW
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hspan

/-- Paper-scale exact equivalence. -/
theorem paperScale_rowPreservation_iff_projectedShiftSpanLeConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M htb hns ↔
    PaperScaleCookLevinOneWindowSingletonQuotientProjectedShiftSpanLeConcreteW
      M htb hns :=
  rowPreservation_iff_projectedShiftSpanLeConcreteW
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four

/-! ## Axiom audit anchors -/

#print axioms projectedShiftSpanLeConcreteW_of_rowPreservation
#print axioms rowPreservation_of_projectedShiftSpanLeConcreteW
#print axioms rowPreservation_iff_projectedShiftSpanLeConcreteW
#print axioms paperScale_rowPreservation_of_projectedShiftSpanLeConcreteW
#print axioms paperScale_rowPreservation_iff_projectedShiftSpanLeConcreteW

end PallLean.Paper93.DeepMath.PathC

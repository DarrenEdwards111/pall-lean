import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedZeroSingletonSpan
import PallLean.Paper93.DeepMath.PathB.ZeroProfileConcreteNormalFormProgress
import PallLean.Paper93.DeepMath.PathB.ConcreteWShiftMlprojClosure

/-!
# One-window zero-profile row map

The remaining singleton-quotient budget needs the zero-profile concrete normal
form at the enlarged Route-C window `log n + 1`.  The old concrete row-embedding
API only exposed the corresponding post-span containment at `log n`.

This file proves the `log n + 1` budget from the exact upgraded containment
statement, making that statement the single local theorem still needed for this
socket.
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

/-- The exact upgraded zero-profile containment needed at the enlarged
one-window radius.  This is the honest replacement for trying to reuse the old
`log n` concreteW row-embedding theorem. -/
def CookLevinOneWindowZeroProfilePostSpanContainment
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) : Prop :=
  allBoundedProfilePostSpan
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n + 1) (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns)
      zeroProfileHistogram ≤
    profileSubspace zeroProfileHistogram (concreteWCanonical n hn4)

/-- The upgraded one-window zero-profile containment gives a concrete row map
for the identity projection at `κ = log n + 1`. -/
noncomputable def zeroProfileConcreteNormalFormRowMap_id_concreteW_oneWindow_of_postSpanContainment
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hpost : CookLevinOneWindowZeroProfilePostSpanContainment
      M n hn htb hns hn4) :
    ZeroProfileConcreteNormalFormRowMap
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (LinearMap.id :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
      (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
        (κ := Nat.log 2 n + 1) hn4) where
  rowNormalForm := fun _ _ _ _ => PUnit.unit
  projected_row_mem_profileSubspace := by
    intro S hS shift hshift
    let factors : Fin (cookLevinFactorList M n hn htb hns).length →
        MvPolynomial (Fin n) ℚ :=
      fun i => (cookLevinFactorList M n hn htb hns).get i
    have hrowSet :
        mlProj (shift * Finset.univ.prod factors) ∈
          zeroProfileShiftImageSet (Nat.log 2 n + 1) factors := by
      simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
        Set.mem_singleton_iff]
      exact ⟨S, hS, shift, hshift, rfl⟩
    have hrowPost :
        mlProj (shift * Finset.univ.prod factors) ∈
          allBoundedProfilePostSpan
            (cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n + 1) (Nat.log 2 n)
            factors
            (cookLevinConstraintType M n hn htb hns)
            zeroProfileHistogram := by
      rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n + 1) (Nat.log 2 n)
        factors
        (cookLevinConstraintType M n hn htb hns)]
      exact Submodule.subset_span hrowSet
    have hmem :
        mlProj (shift * Finset.univ.prod factors) ∈
          profileSubspace zeroProfileHistogram (concreteWCanonical n hn4) :=
      hpost hrowPost
    simpa [LinearMap.id_apply, factors, concreteWCanonical,
      zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW,
      zeroProfileConcreteNormalFormData_singletonZeroProfile,
      zeroProfileConcreteLocalChart_concreteW,
      zeroProfileConcreteLocalChart_of_submoduleFamily] using hmem

/-- One-window projected common span for the identity projection, from the exact
upgraded zero-profile containment. -/
theorem zeroProfileProjectedCommonSpanWithBudget_id_concreteW_oneWindow_of_postSpanContainment
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hpost : CookLevinOneWindowZeroProfilePostSpanContainment
      M n hn htb hns hn4) :
    ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n + 1)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (LinearMap.id :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  zeroProfileProjectedCommonSpanWithBudget_of_concreteRowMap
    (κ := Nat.log 2 n + 1)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (LinearMap.id :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
      (κ := Nat.log 2 n + 1) hn4)
    (zeroProfileConcreteNormalFormRowMap_id_concreteW_oneWindow_of_postSpanContainment
      M n hn htb hns hn4 hpost)

/-- The upgraded one-window zero-profile containment proves the exact
singleton-quotient budget bound needed by the projected zero-profile socket. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_postSpanContainment
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hpost : CookLevinOneWindowZeroProfilePostSpanContainment
      M n hn htb hns hn4) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n + 1) :=
  (zeroProfileSingletonQuotientProjectedTypeBudget_le_of_id_projectedCommonSpan
    (κ := Nat.log 2 n + 1)
    (factors := fun i => (cookLevinFactorList M n hn htb hns).get i)
    (zeroProfileProjectedCommonSpanWithBudget_id_concreteW_oneWindow_of_postSpanContainment
      M n hn htb hns hn4 hpost)).trans
    (zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
      (Nat.log 2 n + 1))

/-- Paper-scale one-window singleton-quotient budget bound from the exact
upgraded zero-profile containment. -/
theorem paperScale_zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_postSpanContainment
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpost : CookLevinOneWindowZeroProfilePostSpanContainment
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four) :
    zeroProfileSingletonQuotientProjectedTypeBudget
        (Nat.log 2 (2 ^ 804) + 1)
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
      withinProfileBound (Nat.log 2 (2 ^ 804) + 1) :=
  zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_postSpanContainment
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hpost

/-- Paper-scale projected zero-profile span from the exact upgraded containment,
via the singleton quotient budget. -/
theorem paperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_postSpanContainment
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpost : CookLevinOneWindowZeroProfilePostSpanContainment
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four) :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M htb hns
      (paperScaleCookLevinSingletonQuotientProjection M htb hns) :=
  paperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_typeBudget
    M htb hns
    (paperScale_zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_postSpanContainment
      M htb hns hpost)

/-! ## Axiom audit anchors -/

#print axioms zeroProfileConcreteNormalFormRowMap_id_concreteW_oneWindow_of_postSpanContainment
#print axioms zeroProfileProjectedCommonSpanWithBudget_id_concreteW_oneWindow_of_postSpanContainment
#print axioms zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_postSpanContainment
#print axioms paperScale_zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_postSpanContainment
#print axioms paperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_postSpanContainment

end PallLean.Paper93.DeepMath.PathC

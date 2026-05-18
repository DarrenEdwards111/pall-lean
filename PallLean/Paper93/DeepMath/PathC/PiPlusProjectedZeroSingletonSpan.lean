import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedPayloadCloseout

/-!
# Singleton-quotient projected zero-profile span for Route C

The old unprojected zero-profile socket is false.  The corrected socket asks for
a projected common span after quotienting the singleton-shift directions.  This
file closes that projected-zero socket from the exact remaining finrank budget
inequality for the singleton quotient.
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

/-- Generic one-window singleton-quotient projected zero-profile common span.
The only remaining arithmetic/local-normal-form burden is that the exact
projected quotient finrank budget fits inside `withinProfileBound`. -/
theorem cookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_typeBudget
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n + 1)
          (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
        withinProfileBound (Nat.log 2 n + 1)) :
    CookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M n hn htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) := by
  exact zeroProfileProjectedCommonSpanWithBudget_mono
    (κ := Nat.log 2 n + 1)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn htb hns).get i))
    (zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_projectedFinrank
      (κ := Nat.log 2 n + 1)
      (factors := fun i => (cookLevinFactorList M n hn htb hns).get i))
    hbudget

/-- Paper-scale singleton-quotient projected zero-profile common span. -/
theorem paperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_typeBudget
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget
          (Nat.log 2 (2 ^ 804) + 1)
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
        withinProfileBound (Nat.log 2 (2 ^ 804) + 1)) :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M htb hns
      (paperScaleCookLevinSingletonQuotientProjection M htb hns) := by
  exact cookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_typeBudget
    M (2 ^ 804) paperScale_ge_two htb hns hbudget

/-- Build the singleton-quotient projected payload once the P-row certificate,
NP-row inclusion, projected zero-profile budget, and active-data package are
available.  This removes the projected-zero field as an independent obligation. -/
noncomputable def singletonQuotientPayloadData_of_typeBudget
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hp : PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      1 0 M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget
          (Nat.log 2 (2 ^ 804) + 1)
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
        withinProfileBound (Nat.log 2 (2 ^ 804) + 1))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (active_data :
      CookLevinOneWindowPerTypeSpanningActiveData
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    PaperScalePiPlusSingletonQuotientPayloadData M htb hns where
  p_windowed_row_certificate := hp
  np_window_row_inclusion := hnp
  projected_zero_common_span :=
    paperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_typeBudget
      M htb hns hbudget
  W := W
  W_finite := W_finite
  W_dim := W_dim
  active_data := active_data

/-! ## Axiom audit anchors -/

#print axioms cookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_typeBudget
#print axioms paperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_singletonQuotient_of_typeBudget
#print axioms singletonQuotientPayloadData_of_typeBudget

end PallLean.Paper93.DeepMath.PathC

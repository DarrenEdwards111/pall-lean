import PallLean.Paper93.DeepMath.PathC.PiPlusStrictCookLevinLift
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedLocalWindowAssembly

/-!
# Strict Pi+ Cook--Levin closeout surface

This file removes one more layer of packaging from the final Route-C endpoint.
A strict Cook--Levin lift can be built from the corrected *windowed row
certificate* plus the NP-window subspace inclusion.  This is the exact form left
after the local two-variable obstruction showed that same-window row transport
is false.

No axiom and no fake `True` field is introduced: the remaining theorem is now
the concrete row identity with one extra derivative window, together with the
NP-side row-space inclusion.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The corrected windowed row certificate supplies the P-side compiled-row
field of the strict Cook--Levin lift. -/
theorem compiledRawPullbackMembership_of_windowedRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP :=
  compiledRawPullbackMembership_of_windowedRawPullbackMembership
    extraK extraL M n hn2 htb hns piP
    (piPlusBooleanProjectedWindowedRawPullbackGeneratorMembership_of_windowedRowCertificate
      extraK extraL M n hn2 htb hns piP hrow)

/-- A strict Cook--Levin lift from the actual two theorem-level row obligations:
windowed P-side row pullback and same-window NP-side subspace preservation. -/
theorem strictCookLevinLift_of_windowedRowCertificate_npInclusion
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hlocal : piP.block_local_hadamard_lift)
    (hrow : PiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M n hn2 htb hns piP)
    (hnp : PiPlusBooleanProjectedNPWindowSubspaceInclusion
      M n hn2 htb hns piP) :
    PiPlusStrictCookLevinBooleanProjectedLift
      extraK extraL M n hn2 htb hns piP where
  block_local := hlocal
  compiled_row_pullback :=
    compiledRawPullbackMembership_of_windowedRowCertificate
      extraK extraL M n hn2 htb hns piP hrow
  np_window_row_space_transport := hnp

/-- Paper-scale specialization for the concrete Cook--Levin block-coordinate
`Pi+` transform. -/
theorem paperScale_strictCookLevinLift_of_windowedRowCertificate_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      1 0 M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
      M htb hns) :
    PaperScalePiPlusStrictCookLevinBooleanProjectedLift M htb hns :=
  strictCookLevinLift_of_windowedRowCertificate_npInclusion
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (cookLevinPiPlusSATTransform_paperScale_blockLocal M htb hns)
    hrow hnp

/-- Active-data closeout from the strict Route-C lift.  This is the final theorem
surface with the nonzero Route-B side in its current smallest local-data form. -/
theorem no_decidesSAT_at_paperScale_of_strictCookLevinLift_activeData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hstrict : PaperScalePiPlusStrictCookLevinBooleanProjectedLift M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_active_data :
      CookLevinOneWindowPerTypeSpanningActiveData
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_localWindowActiveData
    M htb hns
    { route_c_local_window :=
        paperScale_localWindowCertificate_of_cookLevinLocalActionLemma
          M htb hns
          (paperScale_cookLevinLocalActionLemma_of_strictLift
            M htb hns hstrict)
      W := W
      W_finite := W_finite
      W_dim := W_dim
      zero_common_span := zero_common_span
      per_type_active_data := per_type_active_data }

/-- Fully decomposed closeout: replace the strict Route-C lift by its two real
row-space theorem obligations. -/
theorem no_decidesSAT_at_paperScale_of_windowedRowCertificate_npInclusion_activeData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      1 0 M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
      M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_active_data :
      CookLevinOneWindowPerTypeSpanningActiveData
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_strictCookLevinLift_activeData
    M htb hns
    (paperScale_strictCookLevinLift_of_windowedRowCertificate_npInclusion
      M htb hns hrow hnp)
    W W_finite W_dim zero_common_span per_type_active_data

/-! ## Axiom audit anchors -/

#print axioms compiledRawPullbackMembership_of_windowedRowCertificate
#print axioms strictCookLevinLift_of_windowedRowCertificate_npInclusion
#print axioms paperScale_strictCookLevinLift_of_windowedRowCertificate_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_strictCookLevinLift_activeData
#print axioms no_decidesSAT_at_paperScale_of_windowedRowCertificate_npInclusion_activeData

end PallLean.Paper93.DeepMath.PathC

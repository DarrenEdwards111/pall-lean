import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCookLevinLocalAction

/-!
# Paper-scale Boolean-projected Pi+ route

This file names the honest paper-scale Route-C theorem surface after the
formalization mismatch found in the raw `MvPolynomial` ambient.

The paper works Booleanly (`xᵢ² = xᵢ`).  In Lean, the corresponding target is
not raw `Pi+` plus the current `mlProj`-kills-squares behaviour, but the
Boolean-projected gauge

`Pi+ᵦ = zeroProfileBooleanNormalize ∘ Pi+`.

So the P-side theorem to attack is the compiled/windowed Boolean-projected
pullback membership at `(extraK, extraL) = (1, 0)`, or equivalently its compiled
P-subspace inclusion form.  The lemmas below are deliberately kernel-clean
bridges between those exact formulations; they do not assert the remaining
Cook--Levin local algebra for free.
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

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The honest paper-scale Boolean-ambient P-side target, generator form.

This is the named theorem socket Darren identified: prove this for the
Boolean-projected `Pi+ᵦ` gauge, not raw `Pi+` in the full polynomial ambient. -/
abbrev PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
    1 0 M htb hns

/-- The same honest P-side target in the subspace-inclusion form consumed by
rank closure. -/
abbrev PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusion 1 0 M htb hns

/-- Generator-level compiled/windowed Boolean-projected membership immediately
implies the subspace-inclusion formulation at paper scale. -/
theorem paperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero_of_windowedCompiledRawPullbackMembership
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero
      M htb hns :=
  compiledPSubspaceInclusion_of_compiledRawPullbackMembership
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hpull

/-- The two exact Boolean-projected compiled/windowed inclusions assemble into
the local-window Route-C certificate.  This is the compiled-only/windowed row
transport route, with the NP-window side kept explicit. -/
theorem paperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate_of_compiledRawPullbackMembership_and_npSubspaceInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    PaperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate M htb hns where
  p_side_window_transport :=
    paperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero_of_windowedCompiledRawPullbackMembership
      M htb hns hpull
  np_window_preservation := hnp

/-- The same assembly in the already-existing local-action-lemma shape. -/
theorem paperScalePiPlusBooleanProjectedCookLevinLocalActionLemma_of_compiledRawPullbackMembership_and_npSubspaceInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    PaperScalePiPlusBooleanProjectedCookLevinLocalActionLemma M htb hns where
  p_compiled_generator_pullback := hpull
  np_compiled_window_preservation := hnp

/-- Final paper-scale Boolean route package: the Boolean-projected P-side
compiled/windowed pullback membership, the NP-window inclusion, and the existing
Route-B one-window blockers fill the final local-window data. -/
def paperScalePiPlusBooleanProjectedLocalWindowFinalData_of_booleanCompiledRoute
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_spanning :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    PaperScalePiPlusBooleanProjectedLocalWindowFinalData M htb hns where
  route_c_local_window :=
    paperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate_of_compiledRawPullbackMembership_and_npSubspaceInclusion
      M htb hns hpull hnp
  W := W
  W_finite := W_finite
  W_dim := W_dim
  zero_common_span := zero_common_span
  per_type_spanning := per_type_spanning

/-- Once the Boolean-projected compiled/windowed route and Route-B blockers are
proved, the paper-scale SAT contradiction fires. -/
theorem no_decidesSAT_at_paperScale_of_booleanProjectedCompiledRoute
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_spanning :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_localWindowFinalData M htb hns
    (paperScalePiPlusBooleanProjectedLocalWindowFinalData_of_booleanCompiledRoute
      M htb hns hpull hnp W W_finite W_dim zero_common_span per_type_spanning)

/-! ## Axiom audit anchors -/

#print axioms paperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero_of_windowedCompiledRawPullbackMembership
#print axioms paperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate_of_compiledRawPullbackMembership_and_npSubspaceInclusion
#print axioms paperScalePiPlusBooleanProjectedCookLevinLocalActionLemma_of_compiledRawPullbackMembership_and_npSubspaceInclusion
#print axioms paperScalePiPlusBooleanProjectedLocalWindowFinalData_of_booleanCompiledRoute
#print axioms no_decidesSAT_at_paperScale_of_booleanProjectedCompiledRoute

end PallLean.Paper93.DeepMath.PathC

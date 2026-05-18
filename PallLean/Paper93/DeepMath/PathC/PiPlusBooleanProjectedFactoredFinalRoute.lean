import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedFactoredClassifierCloseout
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedPaperScaleRoute

/-!
# Final Route-C bridge from factored product certificate

This file connects the currently sharp P-side product certificate directly to
the existing Boolean-projected paper-scale final route.  The mathematical
payloads remain explicit: the factored row certificate, the NP-window inclusion,
and the Route-B one-window blockers.
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

/-- A paper-scale factored compiled-row certificate supplies the P-side
compiled/windowed raw-pullback membership consumed by the final Boolean Route-C
assembly. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfactored : PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns :=
  paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredCompiledRowCertificate
    M htb hns hfactored

/-- Final closeout stated directly in terms of the sharp factored product
certificate.  Once the factored P-side certificate and NP-window inclusion are
proved, this theorem feeds them into the already-existing final Route-C bridge
with the Route-B one-window blockers. -/
theorem no_decidesSAT_at_paperScale_of_factoredRowCertificate_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfactored : PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
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
  no_decidesSAT_at_paperScale_of_booleanProjectedCompiledRoute
    M htb hns
    (paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredRowCertificate
      M htb hns hfactored)
    hnp W W_finite W_dim zero_common_span per_type_spanning

/-! ## Axiom audit anchors -/

#print axioms paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredRowCertificate
#print axioms no_decidesSAT_at_paperScale_of_factoredRowCertificate_npInclusion

end PallLean.Paper93.DeepMath.PathC

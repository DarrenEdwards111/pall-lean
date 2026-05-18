import PallLean.Paper93.DeepMath.PathC.PiPlusGeneratorPullbackCertificate
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedFactoredFinalRoute

/-!
# P-side closeout from the sharp normalized-product payloads

The current P-side mathematical work has been reduced to two concrete payloads:

1. polynomial-level normalized derivative span;
2. transformed distributed-generator row certificates.

This file wires those two directly into every existing P-side Route-C endpoint:
row-span classifier, windowed raw-pullback membership, compiled P-subspace
inclusion, and the final contradiction bridge when combined with the still
separate NP-side inclusion and Route-B bridge.
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

/-- The two sharp P-side payloads imply the paper-scale factored row-span
classifier. -/
theorem paperScale_factoredRowSpanClassifierOneZero_of_sharpPsidePayloads
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneZero M htb hns :=
  paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_generatorRowCertificate
    M htb hns hpoly hcert

/-- The two sharp P-side payloads imply the windowed compiled raw-pullback
membership socket. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneZero_of_sharpPsidePayloads
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns :=
  paperScale_windowedCompiledRawPullbackMembershipOneZero_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneZero_of_sharpPsidePayloads
      M htb hns hpoly hcert)

/-- The two sharp P-side payloads imply the compiled P-subspace inclusion socket
used by the Route-C final bridge. -/
theorem paperScale_compiledPSubspaceInclusionOneZero_of_sharpPsidePayloads
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero
      M htb hns :=
  paperScale_compiledPSubspaceInclusionOneZero_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneZero_of_sharpPsidePayloads
      M htb hns hpoly hcert)

/-- Final Route-C contradiction bridge using the two sharp P-side payloads rather
than the older factored-row-certificate socket.  The remaining non-P-side
payloads are explicit: NP-window inclusion and the Route-B one-window P-side
rank bridge. -/
theorem no_decidesSAT_at_paperScale_of_sharpPsidePayloads_npInclusion_routeB
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
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
    (paperScale_windowedCompiledRawPullbackMembershipOneZero_of_sharpPsidePayloads
      M htb hns hpoly hcert)
    hnp W W_finite W_dim zero_common_span per_type_spanning

/-! ## Axiom audit anchors -/

#print axioms paperScale_factoredRowSpanClassifierOneZero_of_sharpPsidePayloads
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneZero_of_sharpPsidePayloads
#print axioms paperScale_compiledPSubspaceInclusionOneZero_of_sharpPsidePayloads
#print axioms no_decidesSAT_at_paperScale_of_sharpPsidePayloads_npInclusion_routeB

end PallLean.Paper93.DeepMath.PathC

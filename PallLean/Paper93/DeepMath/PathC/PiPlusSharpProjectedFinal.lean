import PallLean.Paper93.DeepMath.PathC.PiPlusPsideSharpPayloadCloseout
import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedZeroSingletonSpan

/-!
# Sharp projected Route-C final bridge

This file connects the current sharp P-side payloads to the corrected projected
Route-B/NP endpoint.  It avoids the obsolete unprojected zero-profile socket:
the P-side contributes compiled raw-pullback membership, the NP side contributes
row inclusion, and the corrected projected Route-B work contributes the one-window
rank bound directly.
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

/-- Sharp P-side payloads plus NP row inclusion and the corrected projected
Route-B rank bridge fill the final compiled almost-closed endpoint. -/
def oneWindowCompiledAlmostClosedData_of_sharpPsidePayloads_npRow_projectedRouteB
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns)
    (hrouteB : RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns) :
    PaperScalePiPlusBooleanProjectedOneWindowCompiledAlmostClosedData
      M htb hns where
  compiled_pullback_membership :=
    paperScale_windowedCompiledRawPullbackMembershipOneZero_of_sharpPsidePayloads
      M htb hns hpoly hcert
  windowed_p_side_bound := hrouteB
  np_window_rank_nondecreasing :=
    paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
      M htb hns
      (paperScale_npWindowSubspaceInclusion_of_npWindowRowInclusion
        M htb hns hnp)

/-- Final contradiction from the sharp P-side payloads, NP row inclusion, and the
corrected projected Route-B rank bridge. -/
theorem no_decidesSAT_at_paperScale_of_sharpPsidePayloads_npRow_projectedRouteB
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns)
    (hrouteB : RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneWindowCompiledAlmostClosedData
    M htb hns
    (oneWindowCompiledAlmostClosedData_of_sharpPsidePayloads_npRow_projectedRouteB
      M htb hns hpoly hcert hnp hrouteB)

/-! ## Axiom audit anchors -/

#print axioms oneWindowCompiledAlmostClosedData_of_sharpPsidePayloads_npRow_projectedRouteB
#print axioms no_decidesSAT_at_paperScale_of_sharpPsidePayloads_npRow_projectedRouteB

end PallLean.Paper93.DeepMath.PathC

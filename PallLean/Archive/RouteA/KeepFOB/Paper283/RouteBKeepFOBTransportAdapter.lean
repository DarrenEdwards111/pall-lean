import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate
import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.KeepFOBCommonSpanPsideBridge

set_option exponentiation.threshold 1000

/-!
# Route B keepFOB transport adapter

This file connects the concrete flat keepFOB gauge progress back to the Route B
`RouteBFunctorialTransportCertificate` vocabulary.

The file does not construct the final finite-range NFrame `CandidateGauge`.
Instead, it proves that if a selected Route B candidate has the keepFOB flat
SAT-decider projection, then the three Route B transport fields are exactly the
checked keepFOB facts:

* SPDP image containment;
* the unprojected Cook-Levin P-side rank bound, from active profile cases plus
  the non-scalar zero-profile common span;
* the projected NP identity-minor lower bound for keepFOB.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB
open WithinProfileBound

private theorem ge_four_of_ge_two_pow_804 {n : Nat} (hn : n >= 2 ^ 804) :
    n >= 4 := by
  have hfour : (4 : Nat) <= 2 ^ 804 := by
    calc
      (4 : Nat) = 2 ^ 2 := by norm_num
      _ <= 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans hfour hn

/-- Active profile cases plus the non-scalar zero-profile common span supply
the unprojected flat Cook-Levin P-side bound required by the Route B transport
certificate. -/
theorem routeBSATUnprojectedPSideRankBound_of_activeTypeCases_zeroCommonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns :=
  ProfileCompression.p_side_rank_bound_for_cook_levin_of_exactWithinProfileLemma
    M n hn2 htb hns
    (cookLevinExactWithinProfileFinrankLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
      M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn) hzero hblock)

/-- The checked keepFOB projected lower bound is exactly the Route B projected
NP identity-minor lower-bound field for the keepFOB flat SAT gauge. -/
theorem routeBSATProjectedNPIdentityMinorLowerBound_keepFOB
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound
    M n hn hn2 htb hns

/-- If a Route B NFrame candidate's SAT projection is the concrete keepFOB
projection, then active profile cases plus the non-scalar zero-profile common
span discharge all three primitive transport fields.

The remaining construction problem is now isolated in the premise `hPi`: build
the final Route B `CandidateGauge` whose SAT-side action is the keepFOB
projection, or refine the NFrame candidate surface so that the paper's
polynomial-substitution gauge is accepted directly. -/
theorem routeBFunctorialTransportCertificate_of_projection_eq_keepFOB_activeTypeCases_zeroCommonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hPi :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi =
        satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi := by
  refine
    { image_containment := ?_
      unprojected_p_side_rank_bound := ?_
      projected_np_identity_minor_lower_bound := ?_ }
  · simpa [hPi] using
      satDeciderGaugeKeepFOBProjection_spdpSubspaceImageContainment
        M n hn2 htb hns
  · exact
      routeBSATUnprojectedPSideRankBound_of_activeTypeCases_zeroCommonSpan
        M n hn hn2 htb hns hzero hblock
  · simpa [hPi] using
      routeBSATProjectedNPIdentityMinorLowerBound_keepFOB
        M n hn hn2 htb hns

/-! ## Axiom audit anchors -/

#print axioms routeBSATUnprojectedPSideRankBound_of_activeTypeCases_zeroCommonSpan
#print axioms routeBSATProjectedNPIdentityMinorLowerBound_keepFOB
#print axioms routeBFunctorialTransportCertificate_of_projection_eq_keepFOB_activeTypeCases_zeroCommonSpan

end PallLean.Paper93.Paper283

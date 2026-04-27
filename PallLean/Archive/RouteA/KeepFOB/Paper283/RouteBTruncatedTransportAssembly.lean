import PallLean.Archive.RouteA.KeepFOB.Paper283.RouteBKeepFOBTransportAdapter

set_option exponentiation.threshold 1000

/-!
# Route B truncated transport assembly

This file records the SAT-side Route B assembly that is available before a
full finite-range NFrame `CandidateGauge` has been built.

The truncated surface keeps only the action consumed by the Cook-Levin
frontier: a `SATDeciderGaugeMap`, together with the fact that this action is
the checked keepFOB transport.  This is enough to assemble the current
`CookLevinRichProjectionTarget` directly.  If a later NFrame candidate realizes
the same truncated action, the existing keepFOB adapter recovers the current
`RouteBFunctorialTransportCertificate`.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- A refined/truncated Route B transport surface at the SAT frontier.

It deliberately avoids the full NFrame `CandidateGauge` requirement: the
surface only records the SAT-decider gauge action, plus the fact that this
action is the concrete keepFOB projection already checked downstream. -/
structure RouteBTruncatedTransportSurface
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) where
  gauge : SATDeciderGaugeMap M n hn2 htb hns
  gauge_eq_keepFOB :
    gauge = satDeciderGaugeKeepFOBProjection M n hn2 htb hns

/-- The canonical truncated surface whose action is the checked keepFOB
projection. -/
noncomputable def routeBKeepFOBTruncatedTransportSurface
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBTruncatedTransportSurface M n hn2 htb hns where
  gauge := satDeciderGaugeKeepFOBProjection M n hn2 htb hns
  gauge_eq_keepFOB := rfl

/-- The truncated keepFOB surface has the SPDP rank-monotonicity field. -/
theorem routeBTruncatedTransportSurface_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : RouteBTruncatedTransportSurface M n hn2 htb hns) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns S.gauge := by
  simpa [S.gauge_eq_keepFOB] using
    satDeciderGaugeKeepFOBProjection_rankMonotonicity M n hn2 htb hns

/-- Active profile cases plus the non-scalar zero-profile common span supply
the P-side field for any truncated surface whose action is keepFOB. -/
theorem routeBTruncatedTransportSurface_pSideBound_of_activeTypeCases_zeroCommonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : RouteBTruncatedTransportSurface M n hn2 htb hns)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns S.gauge := by
  simpa [S.gauge_eq_keepFOB] using
    satDeciderGaugeKeepFOBProjection_pSideBound_of_activeTypeCases_zeroCommonSpan
      M n hn hn2 htb hns hzero hblock

/-- The checked keepFOB projected lower bound gives the NP identity-minor
field for the truncated surface. -/
theorem routeBTruncatedTransportSurface_npIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : RouteBTruncatedTransportSurface M n hn2 htb hns) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns S.gauge := by
  simpa [S.gauge_eq_keepFOB] using
    satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation
      M n hn hn2 htb hns

/-- The truncated keepFOB transport surface discharges the exact SAT-decider
subgoal package, without producing a full NFrame `CandidateGauge`. -/
theorem routeBTruncatedTransportSurface_subgoals_of_activeTypeCases_zeroCommonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : RouteBTruncatedTransportSurface M n hn2 htb hns)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    SATDeciderGaugeSubgoals M n hn2 htb hns S.gauge :=
  ⟨routeBTruncatedTransportSurface_rankMonotonicity
      M n hn2 htb hns S,
    routeBTruncatedTransportSurface_pSideBound_of_activeTypeCases_zeroCommonSpan
      M n hn hn2 htb hns S hzero hblock,
    routeBTruncatedTransportSurface_npIdentityMinorPreservation
      M n hn hn2 htb hns S⟩

/-- Corrected direct target: the truncated Route B keepFOB transport surface
is already enough for the current Cook-Levin rich projection target.  This
statement avoids the impossible intermediate demand for a full finite-range
NFrame `CandidateGauge`. -/
theorem cookLevinRichProjectionTarget_of_truncatedRouteBTransportSurface_activeTypeCases_zeroCommonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : RouteBTruncatedTransportSurface M n hn2 htb hns)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  ⟨S.gauge,
    routeBTruncatedTransportSurface_subgoals_of_activeTypeCases_zeroCommonSpan
      M n hn hn2 htb hns S hzero hblock⟩

/-- If a full NFrame candidate later realizes the truncated keepFOB action,
the existing keepFOB adapter recovers the current primitive Route B transport
certificate. -/
theorem routeBFunctorialTransportCertificate_of_truncatedRouteBTransportSurface_realizedByCandidate
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : RouteBTruncatedTransportSurface M n hn2 htb hns)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hPi : routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi = S.gauge)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi := by
  exact
    routeBFunctorialTransportCertificate_of_projection_eq_keepFOB_activeTypeCases_zeroCommonSpan
      M n hn hn2 htb hns Pi
      (by rw [hPi, S.gauge_eq_keepFOB])
      hzero hblock

/-- Candidate-realization form of the corrected target, routed through the
current `RouteBFunctorialTransportCertificate` vocabulary. -/
theorem cookLevinRichProjectionTarget_of_truncatedRouteBTransportSurface_realizedByCandidate
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : RouteBTruncatedTransportSurface M n hn2 htb hns)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hPi : routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi = S.gauge)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_transportCertificate
    M n hn hn2 htb hns Pi
    (routeBFunctorialTransportCertificate_of_truncatedRouteBTransportSurface_realizedByCandidate
      M n hn hn2 htb hns S Pi hPi hzero hblock)

end PallLean.Paper93.Paper283

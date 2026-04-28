import PallLean.Paper93.Paper283.RouteBFinalAssembly
import PallLean.Paper93.Paper283.RouteBProjectionRetargetProgress

/-!
# Route B log-window final certificate

This file adds the final Route B certificate surface that the log-window path
actually supports.  It avoids the old promotion through full
`SATDeciderGaugeSPDPSubspaceImageContainment` and avoids deriving the P-side
field from an unprojected P-window bound.

The final `CookLevinRichProjectionTarget` API still asks for rank monotonicity
as one of its three SAT fields.  The corrected certificate therefore supplies
rank monotonicity directly, supplies projected P-side directly, and supplies
the projected NP identity-minor lower bound directly.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Direct SAT-side certificate for one selected Route B NFrame projection.

This is the field package needed by the final target after retargeting away
from the legacy full-SPDP-image route.  The P-side field is already projected;
it is not reconstructed from `RouteBSATUnprojectedPSideRankBound`. -/
structure RouteBDirectSATFieldCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop where
  rank_monotone :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
  projected_p_side :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
  projected_np_identity_minor :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)

/-- Direct SAT fields discharge the final Route B NFrame subgoal package. -/
theorem routeBNFrameGaugeSubgoals_of_directSATFieldCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (cert : RouteBDirectSATFieldCertificate M n hn2 htb hns Pi) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi :=
  ⟨cert.rank_monotone,
    cert.projected_p_side,
    satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
      M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
      cert.projected_np_identity_minor⟩

/-- With direct projected P-side and NP-side fields fixed, the exact remaining
final-target SAT field for the selected projection is rank monotonicity. -/
theorem routeBNFrameGaugeSubgoals_iff_rankMonotonicity_of_directPSide_projectedNP
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hP :
      SATDeciderGaugePSideBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi))
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi <->
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  constructor
  · intro hsub
    exact hsub.1
  · intro hrank
    exact
      routeBNFrameGaugeSubgoals_of_directSATFieldCertificate
        M n hn2 htb hns Pi
        { rank_monotone := hrank
          projected_p_side := hP
          projected_np_identity_minor := hNP }

/-- Log-window Route B per-instance certificate.

This mirrors `RouteBPerInstanceCertificate` on the analytic/rank side but
replaces the old matrix-to-SAT functoriality field with the direct SAT-side
field package above. -/
def RouteBLogWindowFinalCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta normBound logDet delta : Real) (rankA : Nat)
    (eigenvalues : Fin N -> Real)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
      0 < alpha /\ 0 < alpha0 /\ 2 <= gadgetN /\
      0 < theta /\ 0 < normBound /\
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues /\
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet /\
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta rankA /\
      PallLean.Paper93.NFrame.AdmissibleGauge Pi /\
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi /\
      RouteBDirectSATFieldCertificate M n hn2 htb hns Pi

/-- The corrected log-window certificate closes the final rich-projection
target without constructing `RouteBMatrixToSATGaugeFunctoriality`. -/
theorem cookLevinRichProjectionTarget_of_logWindowFinalCertificate
    {M : DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert : RouteBLogWindowFinalCertificate M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, logDet, delta, rankA, eigenvalues, Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm, hspec, hLogLower,
      _hanalytic, _hAdm, _hcompat, hfields⟩
  exact
    cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
      M n hn hn2 htb hns Pi
      (routeBNFrameGaugeSubgoals_of_directSATFieldCertificate
        M n hn2 htb hns Pi hfields)

/-- Uniform log-window final certificates discharge the existing rich
projection frontier. -/
theorem cookLevinRichProjectionDischarge_of_logWindowFinalCertificates
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBLogWindowFinalCertificate M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns hdec
  exact cookLevinRichProjectionTarget_of_logWindowFinalCertificate
    (hn := hn) (hcert M n hn hn2 htb hns hdec)

/-- Contradiction-strength endpoint from uniform log-window final
certificates. -/
theorem noBoundedSATDeciderAtPaperScale_of_logWindowFinalCertificates
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBLogWindowFinalCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mp
    (cookLevinRichProjectionDischarge_of_logWindowFinalCertificates hcert)

/-- The retargeted paper-faithful head-span projection supplies the direct SAT
field package from log-window row closure/descent, direct rank monotonicity,
and the projected NP source minor.  No global admissible-query-log-window
promotion is used here. -/
theorem routeBDirectSATFieldCertificate_of_paperFaithfulPiPhiHeadSpan_frontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
        M n hn2 htb hns)
    (hrank :
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    RouteBDirectSATFieldCertificate M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) := by
  refine
    { rank_monotone := ?_
      projected_p_side := ?_
      projected_np_identity_minor := ?_ }
  · simpa [routeBPaperFaithfulPiPhiHeadSpanProjection] using hrank
  · simpa [routeBPaperFaithfulPiPhiHeadSpanProjection,
      routeBPaperFaithfulPiPhiHeadSpanGauge,
      routeBPaperFaithfulPiPhiHeadSpanTail] using
      routeBRicherSPDPStableCandidate_projectedPSideBound_of_rowClosureDescentFrontier
        M n hn2 htb hns frontier
  · exact
      routeBPaperFaithfulPiPhiHeadSpan_projectedNPIdentityMinorLowerBound_of_source
        M n hn2 htb hns hsource

/-- Constructor for the full log-window final certificate using the
paper-faithful head-span projection. -/
theorem routeBLogWindowFinalCertificate_of_paperFaithfulPiPhiHeadSpan_frontier
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta normBound logDet delta : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hLogLower :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet)
    (hAdm :
      PallLean.Paper93.NFrame.AdmissibleGauge
        (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns))
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA
        (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns))
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
        M n hn2 htb hns)
    (hrank :
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    RouteBLogWindowFinalCertificate M n hn2 htb hns :=
  ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
    theta, normBound, logDet, delta, rankA, eigenvalues,
    routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns,
    halpha, halpha0, hgadgetN, htheta, hnorm, hspec, hLogLower,
    routeBAnalyticRankCoreOutput_of_explicit_routeB_certificate
      alpha beta alpha0 kappa gadgetN G chi Phi
      halpha halpha0 hgadgetN htheta hnorm hspec hLogLower,
    hAdm, hcompat,
    routeBDirectSATFieldCertificate_of_paperFaithfulPiPhiHeadSpan_frontier
      M n hn2 htb hns frontier hrank hsource⟩

/-- Diagnostic for the legacy per-instance certificate: the old Route B
certificate type still forces both full SPDP image containment and an
unprojected P-side rank bound.  This is exactly the API mismatch avoided by
`RouteBLogWindowFinalCertificate`. -/
theorem routeBPerInstanceCertificate_forces_legacy_spdp_unprojected_fields
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert : RouteBPerInstanceCertificate M n hn2 htb hns) :
    exists Pi : PallLean.Paper93.NFrame.CandidateGauge
        (RouteBCookLevinDim M n hn2 htb hns),
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) /\
      RouteBSATUnprojectedPSideRankBound M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, logDet, delta, rankA, eigenvalues, Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm, hspec, hLogLower,
      _hAdm, hcompat, hfun⟩
  refine ⟨Pi, hfun.spdp_image_containment, ?_⟩
  exact hfun.pSide_of_routeB_rank
    (routeBAnalyticRankCoreOutput_of_explicit_routeB_certificate
      alpha beta alpha0 kappa gadgetN G chi Phi
      halpha halpha0 hgadgetN htheta hnorm hspec hLogLower)
    hcompat

/-! ## Axiom audit anchors -/

#print axioms RouteBDirectSATFieldCertificate
#print axioms routeBNFrameGaugeSubgoals_of_directSATFieldCertificate
#print axioms routeBNFrameGaugeSubgoals_iff_rankMonotonicity_of_directPSide_projectedNP
#print axioms RouteBLogWindowFinalCertificate
#print axioms cookLevinRichProjectionTarget_of_logWindowFinalCertificate
#print axioms cookLevinRichProjectionDischarge_of_logWindowFinalCertificates
#print axioms noBoundedSATDeciderAtPaperScale_of_logWindowFinalCertificates
#print axioms routeBDirectSATFieldCertificate_of_paperFaithfulPiPhiHeadSpan_frontier
#print axioms routeBLogWindowFinalCertificate_of_paperFaithfulPiPhiHeadSpan_frontier
#print axioms routeBPerInstanceCertificate_forces_legacy_spdp_unprojected_fields

end PallLean.Paper93.Paper283

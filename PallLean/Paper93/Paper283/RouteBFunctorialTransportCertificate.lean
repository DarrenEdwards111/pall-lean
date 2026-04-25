import PallLean.Paper93.Paper283.RouteBMatrixToSATGauge

/-!
# Route B functorial transport certificate

This file factors the Route B matrix-to-SAT functoriality hypothesis through
the primitive SAT-side transport obligations that are already exposed by the
SAT-decider gauge bridge files:

* SPDP subspace image containment;
* the unprojected flat Cook-Levin P-side rank bound;
* the projected NP identity-minor lower bound.

The certificate is deliberately independent of the Route B analytic parameters.
Once those three concrete facts are supplied for a selected NFrame projection,
they construct the older `RouteBMatrixToSATGaugeFunctoriality` package for any
Route B analytic surface.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- The concrete SAT-side transport certificate for a selected Route B NFrame
projection.

This is the smallest package needed by the checked SAT-decider bridge lemmas:
image containment gives rank monotonicity, the unprojected P-side bound gives
the projected P-side field by rank monotonicity, and the projected lower bound
gives NP identity-minor preservation. -/
structure RouteBFunctorialTransportCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop where
  image_containment :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
  unprojected_p_side_rank_bound :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns
  projected_np_identity_minor_lower_bound :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)

/-- The primitive transport certificate constructs the older Route B
matrix-to-SAT functoriality package.  The analytic rank output and projection
rank compatibility arguments are no longer mathematical inputs here; the
P-side and NP-side facts are already the concrete SAT-side obligations. -/
theorem routeBMatrixToSATGaugeFunctoriality_of_transportCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcert :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    RouteBMatrixToSATGaugeFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi := by
  refine
    { spdp_image_containment := hcert.image_containment
      pSide_of_routeB_rank := ?_
      npIdentityMinor_of_routeB_rank := ?_ }
  · intro _hanalytic _hcompat
    exact hcert.unprojected_p_side_rank_bound
  · intro _hanalytic _hcompat
    exact hcert.projected_np_identity_minor_lower_bound

/-- Conversely, once the checked Route B analytic output and projection-rank
compatibility are available, the older functoriality package yields the
primitive certificate. -/
theorem transportCertificate_of_routeBMatrixToSATGaugeFunctoriality
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi :=
  { image_containment := hfun.spdp_image_containment
    unprojected_p_side_rank_bound :=
      hfun.pSide_of_routeB_rank hanalytic hcompat
    projected_np_identity_minor_lower_bound :=
      hfun.npIdentityMinor_of_routeB_rank hanalytic hcompat }

/-- With the Route B analytic output and projection-rank compatibility fixed,
the older functoriality hypothesis is equivalent to the primitive transport
certificate. -/
theorem routeBMatrixToSATGaugeFunctoriality_iff_transportCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi) :
    RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi <->
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi := by
  constructor
  · intro hfun
    exact transportCertificate_of_routeBMatrixToSATGaugeFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi hanalytic hcompat hfun
  · intro hcert
    exact routeBMatrixToSATGaugeFunctoriality_of_transportCertificate
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi hcert

/-- The primitive transport certificate directly discharges the three SAT
subgoals for the selected Route B NFrame projection. -/
theorem routeBNFrameGaugeSubgoals_of_transportCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcert :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
        M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
        hcert.image_containment
  · exact
      satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
        M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
        (satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
          M n hn2 htb hns
          (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
          hcert.image_containment)
        hcert.unprojected_p_side_rank_bound
  · exact
      satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
        M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
        hcert.projected_np_identity_minor_lower_bound

/-- The primitive transport certificate is enough for the older broad
matrix-rank-to-SAT gauge hypothesis. -/
theorem routeBMatrixRankToSATGaugeHypothesis_of_transportCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcert :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    RouteBMatrixRankToSATGaugeHypothesis
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi := by
  intro _hanalytic
  exact routeBNFrameGaugeSubgoals_of_transportCertificate
    M n hn2 htb hns Pi hcert

/-- Package the primitive certificate as the existing Route B NFrame gauge
package, retaining the NFrame admissibility side condition separately. -/
theorem routeBNFrameGaugePackage_of_transportCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcert :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    RouteBNFrameGaugePackage M n hn2 htb hns :=
  ⟨Pi, hAdm,
    routeBNFrameGaugeSubgoals_of_transportCertificate
      M n hn2 htb hns Pi hcert⟩

/-- The primitive certificate supplies the existing Cook-Levin rich projection
target for the selected Route B projection. -/
theorem cookLevinRichProjectionTarget_of_transportCertificate
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcert :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    M n hn hn2 htb hns Pi
    (routeBNFrameGaugeSubgoals_of_transportCertificate
      M n hn2 htb hns Pi hcert)

/-! ## Axiom audit anchors -/

#print axioms routeBMatrixToSATGaugeFunctoriality_of_transportCertificate
#print axioms transportCertificate_of_routeBMatrixToSATGaugeFunctoriality
#print axioms routeBMatrixToSATGaugeFunctoriality_iff_transportCertificate
#print axioms routeBNFrameGaugeSubgoals_of_transportCertificate
#print axioms routeBMatrixRankToSATGaugeHypothesis_of_transportCertificate
#print axioms routeBNFrameGaugePackage_of_transportCertificate
#print axioms cookLevinRichProjectionTarget_of_transportCertificate

end PallLean.Paper93.Paper283

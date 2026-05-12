import PallLean.Paper93.Paper283.RouteBConstantsGaugeCertificate

/-!
# Route B constants-gauge P-side transport

This file records the Route B/NFrame-only P-side facts available for the
selected constants gauge.  The constants projection gives SPDP image
containment and the projected SAT P-side bound directly; no profile-collapse
or `keepFOB` surface is used.

It also names the exact remaining criterion for the current primitive
`RouteBFunctorialTransportCertificate`: that structure's P-side field is the
unprojected flat Cook-Levin bound, so the missing input is an analytic-to-SPDP
bridge from the Route B rank surface to `RouteBSATUnprojectedPSideRankBound`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

private theorem one_le_log_two_of_two_le {n : Nat} (hn2 : n >= 2) :
    1 <= Nat.log 2 n := by
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by simpa using hn2)

/-- The constants NFrame projection satisfies the concrete SPDP image
containment criterion used by the SAT gauge rank-monotonicity bridge. -/
theorem routeBConstantsGauge_spdpSubspaceImageContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBConstantsGauge M n hn2 htb hns)) := by
  intro k l p
  unfold routeBNFrameCandidateAsSATGauge routeBConstantsGauge
    routeBConstantsCandidateGauge
  rw [PallLean.Paper93.NFrame.nonTrivialGauge_projection_eq_piStarConcrete]
  exact PallLean.Paper93.Substantive.mlBlockedSpdpSubspace_piStarConcrete_le_map
    (cook_levin_compilation M n hn2 htb hns).partition k l p

/-- Rank monotonicity for the constants Route B gauge, derived from the
NFrame constants-projection image-containment theorem. -/
theorem routeBConstantsGauge_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBConstantsGauge M n hn2 htb hns)) :=
  satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
    M n hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
      (routeBConstantsGauge M n hn2 htb hns))
    (routeBConstantsGauge_spdpSubspaceImageContainment M n hn2 htb hns)

/-- The constants Route B gauge has the projected SAT P-side rank bound
directly from the NFrame constants-projection rank collapse.  This is a
projected fact; it does not prove the unprojected flat Cook-Levin bound. -/
theorem routeBConstantsGauge_projectedPSideBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBConstantsGauge M n hn2 htb hns)) := by
  unfold SATDeciderGaugePSideBound routeBNFrameCandidateAsSATGauge
    routeBConstantsGauge routeBConstantsCandidateGauge
  rw [PallLean.Paper93.NFrame.nonTrivialGauge_projection_eq_piStarConcrete]
  exact le_trans
    (PallLean.Paper93.Substantive.piStar_rank_bounded
      (N := RouteBCookLevinDim M n hn2 htb hns)
      (B := (cook_levin_compilation M n hn2 htb hns).partition)
      (κ := Nat.log 2 n) (ℓ := Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns))
      (one_le_log_two_of_two_le hn2))
    (Nat.zero_le (n ^ 200))

/-- The exact P-side analytic-to-SPDP bridge still needed to fill the current
primitive transport certificate for the constants gauge.

The constants projection already proves the projected P-side field above.
However, `RouteBFunctorialTransportCertificate.unprojected_p_side_rank_bound`
asks for the stronger unprojected Cook-Levin SPDP estimate.  This predicate is
that missing Route B analytic-to-SPDP conversion, specialised to the constants
gauge and without importing profile compression or `keepFOB`. -/
def RouteBConstantsGaugeAnalyticToUnprojectedSPDPBridge {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat) : Prop :=
  RouteBAnalyticRankCoreOutput
      alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA ->
    RouteBProjectionRankCompatible M n hn2 htb hns rankA
      (routeBConstantsGauge M n hn2 htb hns) ->
      RouteBSATUnprojectedPSideRankBound M n hn2 htb hns

/-- Criterion form for the constants-gauge P-side field of
`RouteBFunctorialTransportCertificate`: an analytic-to-SPDP bridge supplies
exactly the currently required unprojected P-side proposition. -/
theorem routeBConstantsGauge_unprojectedPSideRankBound_of_analyticToSPDPBridge
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA
        (routeBConstantsGauge M n hn2 htb hns))
    (hbridge :
      RouteBConstantsGaugeAnalyticToUnprojectedSPDPBridge
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns :=
  hbridge hanalytic hcompat

/-- Once the P-side analytic-to-SPDP bridge and the NP projected lower bound
are supplied, the constants gauge satisfies the primitive Route B transport
certificate.  The image-containment field is proved above from Route B/NFrame
content; the P-side field is exactly the named bridge criterion. -/
theorem routeBConstantsGauge_transportCertificate_of_analyticToSPDPBridge
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA
        (routeBConstantsGauge M n hn2 htb hns))
    (hPbridge :
      RouteBConstantsGaugeAnalyticToUnprojectedSPDPBridge
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBConstantsGauge M n hn2 htb hns))) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns
      (routeBConstantsGauge M n hn2 htb hns) :=
  { image_containment :=
      routeBConstantsGauge_spdpSubspaceImageContainment M n hn2 htb hns
    unprojected_p_side_rank_bound :=
      routeBConstantsGauge_unprojectedPSideRankBound_of_analyticToSPDPBridge
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA hanalytic hcompat hPbridge
    projected_np_identity_minor_lower_bound := hNP }

/-- For the constants gauge, the primitive transport certificate is equivalent
to the two rank facts not already supplied by NFrame image containment.  This
is the sharp local obstruction: the P-side component is precisely the
unprojected Cook-Levin SPDP bound, not the projected constants-gauge collapse. -/
theorem routeBConstantsGauge_transportCertificate_iff_unprojectedPside_and_np
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns
        (routeBConstantsGauge M n hn2 htb hns) <->
      RouteBSATUnprojectedPSideRankBound M n hn2 htb hns /\
        RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
          (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBConstantsGauge M n hn2 htb hns)) := by
  constructor
  · intro hcert
    exact ⟨hcert.unprojected_p_side_rank_bound,
      hcert.projected_np_identity_minor_lower_bound⟩
  · intro h
    exact
      { image_containment :=
          routeBConstantsGauge_spdpSubspaceImageContainment M n hn2 htb hns
        unprojected_p_side_rank_bound := h.1
        projected_np_identity_minor_lower_bound := h.2 }

/-! ## Axiom audit anchors -/

#print axioms routeBConstantsGauge_spdpSubspaceImageContainment
#print axioms routeBConstantsGauge_rankMonotonicity
#print axioms routeBConstantsGauge_projectedPSideBound
#print axioms routeBConstantsGauge_unprojectedPSideRankBound_of_analyticToSPDPBridge
#print axioms routeBConstantsGauge_transportCertificate_of_analyticToSPDPBridge
#print axioms routeBConstantsGauge_transportCertificate_iff_unprojectedPside_and_np

end PallLean.Paper93.Paper283

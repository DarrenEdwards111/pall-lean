import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate

/-!
# Route B SPDP image containment reduction

This file isolates the first field of
`RouteBFunctorialTransportCertificate` for the concrete Route B / Cook-Levin
projection surface.  The remaining content is reduced to a generator-image
transport statement on the exact Cook-Levin SPDP partition and the selected
NFrame candidate projection.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Generator-level Route B SPDP transport for the selected NFrame candidate.

For every Cook-Levin SPDP generator after applying the candidate projection,
the generator must already be the candidate projection of an element of the
unprojected Cook-Levin SPDP subspace.  This is the concrete remaining
linear-algebra check behind the `image_containment` certificate field. -/
def RouteBSPDPGeneratorImageTransport
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  forall (kappa ell : Nat)
    (p : MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (m : MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat),
    S.length = kappa ->
    m.totalDegree <= ell ->
    m.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    mlProj
        (m * SPDP.iterDerivList S
          ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p)) ∈
      Submodule.map
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          kappa ell p)

/-- The generator-level Route B transport discharges the concrete
SAT-decider SPDP image-containment field for the selected NFrame projection. -/
theorem routeBSPDPImageContainment_of_generatorImageTransport
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hgen : RouteBSPDPGeneratorImageTransport M n hn2 htb hns Pi) :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  exact
    spdpSubspaceImageContainment_of_generator_image_mem
      (cook_levin_compilation M n hn2 htb hns).partition
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
      hgen

/-- Image containment implies the generator-level Route B transport condition.
This records that the new generator condition is not stronger than the actual
certificate field; it is exactly the generator-checking form of that field. -/
theorem generatorImageTransport_of_routeBSPDPImageContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcontain :
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)) :
    RouteBSPDPGeneratorImageTransport M n hn2 htb hns Pi := by
  intro kappa ell p S m hSlen hmdeg hmvars hadm
  exact hcontain kappa ell p
    (Submodule.subset_span
      ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩)

/-- The Route B generator-image transport is equivalent to the SPDP
image-containment certificate field for the selected Cook-Levin projection. -/
theorem routeBSPDPGeneratorImageTransport_iff_imageContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) :
    RouteBSPDPGeneratorImageTransport M n hn2 htb hns Pi <->
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  constructor
  · exact routeBSPDPImageContainment_of_generatorImageTransport
      M n hn2 htb hns Pi
  · exact generatorImageTransport_of_routeBSPDPImageContainment
      M n hn2 htb hns Pi

/-- A generator-image proof supplies the `image_containment` field of the
primitive Route B transport certificate; the P-side and NP-side certificate
fields remain the existing concrete SAT-side obligations. -/
theorem routeBFunctorialTransportCertificate_of_generatorImageTransport
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hgen : RouteBSPDPGeneratorImageTransport M n hn2 htb hns Pi)
    (hpSide : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi :=
  { image_containment :=
      routeBSPDPImageContainment_of_generatorImageTransport
        M n hn2 htb hns Pi hgen
    unprojected_p_side_rank_bound := hpSide
    projected_np_identity_minor_lower_bound := hNP }

/-- The same generator-image reduction feeds directly into the existing
Route B NFrame gauge subgoal package once the other two SAT-side transport
facts are supplied. -/
theorem routeBNFrameGaugeSubgoals_of_generatorImageTransport
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hgen : RouteBSPDPGeneratorImageTransport M n hn2 htb hns Pi)
    (hpSide : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi :=
  routeBNFrameGaugeSubgoals_of_transportCertificate M n hn2 htb hns Pi
    (routeBFunctorialTransportCertificate_of_generatorImageTransport
      M n hn2 htb hns Pi hgen hpSide hNP)

/-! ## Axiom audit anchors -/

#print axioms routeBSPDPImageContainment_of_generatorImageTransport
#print axioms generatorImageTransport_of_routeBSPDPImageContainment
#print axioms routeBSPDPGeneratorImageTransport_iff_imageContainment
#print axioms routeBFunctorialTransportCertificate_of_generatorImageTransport
#print axioms routeBNFrameGaugeSubgoals_of_generatorImageTransport

end PallLean.Paper93.Paper283

import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteNP
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowCover
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.PeqNPBridge

/-!
# Route-B transport seam closure (paper-faithful, conditional)

This file proves a concrete conditional seam:
if a uniform Route-B transport certificate exists for bounded SAT-decider
machines, then the integrated rich-projection target is discharged, hence no
bounded SAT decider exists at paper scale, hence `PeqNP_Paper` is contradictory.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.Paper283

/-- Uniform Route-B transport seam hypothesis (certificate form). -/
abbrev RouteBTransportCertificateSeam : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M),
    ∃ (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi

/-- Bridge theorem: if the richer finite-row concrete NP surface is available
uniformly (SPDP containment + P-window cover), then the Route-B transport
certificate seam exists. -/
theorem routeBTransportCertificateSeam_of_richerConcreteNP_surface
    (hcontain :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)))
    (hcover :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    RouteBTransportCertificateSeam := by
  intro M n hn hn2 htb hns hdec
  refine ⟨routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
    (routeBRicherConcreteNPWitnessRows M n hn2 htb hns), ?_⟩
  exact routeBRicherConcreteNP_transportCertificate M n hn hn2 htb hns
    (hcontain M n hn hn2 htb hns hdec)
    (hcover M n hn hn2 htb hns hdec)

/-- The transport certificate seam discharges the integrated Route-B final
projection target for all bounded SAT-decider machines. -/
theorem cookLevinRichProjectionDischarge_of_transportCertificateSeam
    (hSeam : RouteBTransportCertificateSeam) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns hdec
  rcases hSeam M n hn hn2 htb hns hdec with ⟨Pi, hcert⟩
  exact cookLevinRichProjectionTarget_of_transportCertificate
    M n hn hn2 htb hns Pi hcert

/-- The transport certificate seam rules out bounded SAT deciders at paper
scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_transportCertificateSeam
    (hSeam : RouteBTransportCertificateSeam) :
    NoBoundedSATDeciderAtPaperScale :=
  (cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mp
    (cookLevinRichProjectionDischarge_of_transportCertificateSeam hSeam))

/-- Paper-faithful contradiction form from the transport seam. -/
theorem not_PeqNP_of_transportCertificateSeam
    (hSeam : RouteBTransportCertificateSeam) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_transportCertificateSeam hSeam)

/-- Direct closeout from the richer concrete NP surface assumptions. -/
theorem not_PeqNP_of_richerConcreteNP_surface
    (hcontain :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)))
    (hcover :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    ∀ (_ : PeqNP_Paper), False :=
  not_PeqNP_of_transportCertificateSeam
    (routeBTransportCertificateSeam_of_richerConcreteNP_surface hcontain hcover)

/-- Closeout with the P-window side discharged by active-template blockers. -/
theorem not_PeqNP_of_richerConcreteNP_surface_activeTemplateBlockers
    (hcontain :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)))
    (hblock :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinActiveProfileTemplateCollapseBlockers M n hn2 htb hns) :
    ∀ (_ : PeqNP_Paper), False := by
  apply not_PeqNP_of_richerConcreteNP_surface hcontain
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := by
    have hpow : (4 : Nat) ≤ 2 ^ 804 := by
      native_decide
    exact le_trans hpow hn
  exact routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTemplateBlockers
    M n hn2 htb hns hn4 (hblock M n hn hn2 htb hns)

#print axioms routeBTransportCertificateSeam_of_richerConcreteNP_surface
#print axioms cookLevinRichProjectionDischarge_of_transportCertificateSeam
#print axioms noBoundedSATDeciderAtPaperScale_of_transportCertificateSeam
#print axioms not_PeqNP_of_transportCertificateSeam
#print axioms not_PeqNP_of_richerConcreteNP_surface
#print axioms not_PeqNP_of_richerConcreteNP_surface_activeTemplateBlockers

end PallLean.Paper93.DeepMath.PathB

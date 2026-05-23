import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteNP
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowCover
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteScalarClosure
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

/-- Closeout with SPDP side reduced to compiledPoly scalar row-closure
plus unprojected preimage closure, and P-window side discharged by
active-template blockers. -/
theorem not_PeqNP_of_richerConcreteNP_scalarPreimage_activeTemplateBlockers
    (hscalar :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        RouteBRicherConcreteNPCompiledPolyScalarRowClosure M n hn2 htb hns)
    (hunprojected :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure M n hn2 htb hns)
    (hblock :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinActiveProfileTemplateCollapseBlockers M n hn2 htb hns) :
    ∀ (_ : PeqNP_Paper), False := by
  apply not_PeqNP_of_richerConcreteNP_surface_activeTemplateBlockers
  · intro M n hn hn2 htb hns hdec
    exact routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure
      M n hn2 htb hns
      (hscalar M n hn hn2 htb hns)
      (hunprojected M n hn hn2 htb hns)
  · exact hblock

/-- Under the paper bundle witness (`PeqNP_Paper`), the uniform scalar-row
closure premise is inconsistent: it is refuted at the bundled decider by the
concrete coefficient obstruction theorem. -/
theorem not_uniform_richerConcreteNP_scalarClosure_at_paperScale_of_PeqNP
    (hPeq : PeqNP_Paper)
    (hscalar :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        RouteBRicherConcreteNPCompiledPolyScalarRowClosure M n hn2 htb hns) :
    False := by
  let M0 : DTM := hPeq.decider
  let n0 : Nat := 2 ^ 804
  have hn0 : n0 ≥ 2 ^ 804 := by simp [n0]
  have hn20 : n0 ≥ 2 := by
    have hpow : (2 : Nat) ≤ 2 ^ 804 := by
      native_decide
    simpa [n0] using hpow
  have htb0 : M0.timeBound ≤ 4 := by
    simpa [M0] using hPeq.timeBound_le
  have hns0 : M0.numStates ≤ n0 := by
    simpa [M0, n0] using hPeq.numStates_bound
  exact
    (not_routeBRicherConcreteNPCompiledPolyScalarRowClosure M0 n0 hn20 htb0 hns0)
      (hscalar M0 n0 hn0 hn20 htb0 hns0)

#print axioms routeBTransportCertificateSeam_of_richerConcreteNP_surface
#print axioms cookLevinRichProjectionDischarge_of_transportCertificateSeam
#print axioms noBoundedSATDeciderAtPaperScale_of_transportCertificateSeam
#print axioms not_PeqNP_of_transportCertificateSeam
#print axioms not_PeqNP_of_richerConcreteNP_surface
#print axioms not_PeqNP_of_richerConcreteNP_surface_activeTemplateBlockers
#print axioms not_PeqNP_of_richerConcreteNP_scalarPreimage_activeTemplateBlockers
#print axioms not_uniform_richerConcreteNP_scalarClosure_at_paperScale_of_PeqNP

end PallLean.Paper93.DeepMath.PathB

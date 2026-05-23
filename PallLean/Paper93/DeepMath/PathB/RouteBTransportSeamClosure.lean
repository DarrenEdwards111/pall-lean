import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate
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

#print axioms cookLevinRichProjectionDischarge_of_transportCertificateSeam
#print axioms noBoundedSATDeciderAtPaperScale_of_transportCertificateSeam
#print axioms not_PeqNP_of_transportCertificateSeam

end PallLean.Paper93.DeepMath.PathB

import PallLean.Paper93.Paper283.RouteBTransportSPDPContainment
import PallLean.Paper93.Paper283.RouteBConstantsGaugeCertificate

/-!
# Route B constants gauge SPDP transport

This file specializes the SPDP image-containment theorem from
`RouteBTransportSPDPContainment` to the named `routeBConstantsGauge` abbrev.
The proof is the same kernel-only constants-projection transport for
`routeBConstantsCandidateGauge`; no Route A profile or keepFOB surface is used.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- The named Route B constants gauge satisfies the primitive SAT-side SPDP
image-containment field. -/
theorem routeBConstantsGauge_spdpImageContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBConstantsGauge M n hn2 htb hns)) :=
  routeBConstantsCandidateGauge_spdpImageContainment M n hn2 htb hns

/-- The named constants gauge satisfies the generator-image transport
criterion equivalent to SPDP image containment. -/
theorem routeBConstantsGauge_generatorImageTransport
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBSPDPGeneratorImageTransport M n hn2 htb hns
      (routeBConstantsGauge M n hn2 htb hns) :=
  routeBConstantsCandidateGauge_generatorImageTransport M n hn2 htb hns

/-- For the named constants gauge, the primitive Route B transport certificate
now reduces to the separated P-side and NP-side SAT transport fields. -/
theorem routeBConstantsGauge_transportCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hpSide : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBConstantsGauge M n hn2 htb hns))) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns
      (routeBConstantsGauge M n hn2 htb hns) :=
  routeBConstantsCandidateGauge_transportCertificate
    M n hn2 htb hns hpSide hNP

/-! ## Axiom audit anchors -/

#print axioms routeBConstantsGauge_spdpImageContainment
#print axioms routeBConstantsGauge_generatorImageTransport
#print axioms routeBConstantsGauge_transportCertificate

end PallLean.Paper93.Paper283

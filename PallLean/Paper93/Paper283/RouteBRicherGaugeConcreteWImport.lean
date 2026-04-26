import PallLean.Paper93.Paper283.RouteBRicherGaugeCorrectedConcreteNPAssembly
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowConcreteWReduction

/-!
# Route B concreteW import adapter

This file keeps the final finite-row Route B surface close to the existing
strongest direct concreteW branch theorem.  The adapter imports the checked
direct-branch/H4/I1-I2-I3 row-embedding reduction and feeds it into the
concrete-NP SPDP map-preimage certificate wrapper.
-/

namespace PallLean.Paper93.Paper283

open TuringMachine (DTM)
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)

attribute [local instance] Classical.dec

/-- Import adapter for the strongest checked direct concreteW row-embedding
surface currently present in `Paper283`.

The proof is intentionally only a named forwarding step: direct branch-shape
witnesses plus canonical-row transport close H3, H4 is kept explicit, and the
existing I1/I2/I3 composition closes I5. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_of_importedDirectBranch_H4_I123
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4 :=
  CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I123
    M n hn htb hns hn4 hShape hTransport hDeriv hI1 hI2 hI3

/-- Concrete-NP finite-row Route B certificate with the row-embedding input
discharged through the imported direct concreteW branch theorem.

The remaining assumptions are the finite-row SPDP map-preimage for the
prepended concrete-NP rows and the concreteW branch/transport/H4/I1-I2-I3
inputs needed by the existing direct row-embedding reduction. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_importedConcreteW_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_rowEmbeddings_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    preimage
    (CookLevinPerTypeRowEmbeddings_concreteW_of_importedDirectBranch_H4_I123
      M n hn2 htb hns hn4 hShape hTransport hDeriv hI1 hI2 hI3)

/-! ## Axiom audit anchors -/

#print axioms CookLevinPerTypeRowEmbeddings_concreteW_of_importedDirectBranch_H4_I123
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_importedConcreteW_deltaEqRateKappa

end PallLean.Paper93.Paper283

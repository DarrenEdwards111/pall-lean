import PallLean.Paper93.Paper283.RouteBRicherGaugeFiniteRowsSPDPCommutationBridge
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteWChargedClosure

/-!
# Corrected finite-row Route B assembly

This module combines the two corrected Route B frontiers:

* finite-row SPDP image containment is discharged from generator commutation;
* the P-window cover is supplied by the endpoint/charged, non-scalar
  zero-profile route rather than the old scalar/template collapse surface.
-/

namespace PallLean.Paper93.Paper283

open TuringMachine
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.Closure
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Finite-row Route B assembly using generator commutation for the SPDP
preimage side and an already-packaged endpoint/charged P-window bridge for the
P-side cover.

This is the corrected combined surface: it does not use the old scalar
zero-profile collapse or canonical-H4 route. -/
theorem routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPGeneralCommutation_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hcomm bridge.cover Q i hrow hextract hsource

/-- Cardinality-bound variant of the corrected combined Route B surface.

The live-profile side is represented by active blockers.  The zero-profile
side is the non-scalar common-span package with a concrete cardinality budget.
-/
theorem routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_activeBlockersZeroNonScalar_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4))
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hcomm
    (routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarCardBound
      M n hn2 htb hns hn4 charge hI1 hI2c hI3 hbound hactive)
    Q i hrow hextract hsource

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_activeBlockersZeroNonScalar_deltaEqRateKappa

end PallLean.Paper93.Paper283

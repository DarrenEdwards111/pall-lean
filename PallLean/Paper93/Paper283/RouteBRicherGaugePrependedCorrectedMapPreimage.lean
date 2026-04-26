import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteMapPreimage

/-!
# Corrected prepended-row map-preimage assembly

This module combines the newest concrete-NP prepended finite-row SPDP
map-preimage surface with the corrected P-window surfaces.

The point is to keep the SPDP side on the finite-row map-preimage route and
the P-side on the endpoint/charged or active-blocker/non-scalar profile route,
instead of falling back to the older canonical `concreteW` H4/transport
adapter.
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

/-- Finite-row Route B assembly using the map-preimage SPDP surface and an
already-packaged endpoint/charged P-window bridge.

This is the map-preimage sibling of
`routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa`.
-/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
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
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows)
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
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    preimage bridge.cover Q i hrow hextract hsource

/-- Finite-row Route B assembly using the map-preimage SPDP surface and the
corrected active-blocker/non-scalar zero-profile P-window cover.

This avoids the older canonical `concreteW` row-embedding input entirely at
this assembly layer. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
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
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows)
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
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    preimage
    (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarCardBound
      M n hn2 htb hns hn4 hbound hactive)
    Q i hrow hextract hsource

/-- Concrete-NP prepended finite-row Route B certificate from the map-preimage
SPDP surface and an endpoint/charged P-window bridge. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
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
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    preimage bridge
    (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
    0
    (routeBRicherConcreteNPPrependedRows_zero_eq_embed
      M n hn2 htb hns tail)
    (routeBRicherConcreteNP_extracts_compiled_for_rows
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
      M n hn hn2 htb hns)

/-- Concrete-NP prepended finite-row Route B certificate from map-preimage and
the corrected active-blocker/non-scalar P-window cover. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
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
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hbound hactive preimage
    (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
    0
    (routeBRicherConcreteNPPrependedRows_zero_eq_embed
      M n hn2 htb hns tail)
    (routeBRicherConcreteNP_extracts_compiled_for_rows
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
      M n hn hn2 htb hns)

/-- Concrete-NP prepended finite-row Route B certificate from the explicit
head/tail row-closure package, unprojected preimage, and endpoint/charged
P-window bridge. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_endpointChargedBridge_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
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
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (unprojectedPreimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_unprojectedPreimage
      M n hn2 htb hns tail pkg unprojectedPreimage)
    bridge

/-- Concrete-NP prepended finite-row Route B certificate from the explicit
head/tail row-closure package, unprojected preimage, and corrected
active-blocker/non-scalar P-window cover. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
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
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (unprojectedPreimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hbound hactive
    (routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_unprojectedPreimage
      M n hn2 htb hns tail pkg unprojectedPreimage)

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa

end PallLean.Paper93.Paper283

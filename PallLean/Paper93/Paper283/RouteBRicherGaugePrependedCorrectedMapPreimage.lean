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

/-- Finite-row Route B assembly using the map-preimage SPDP surface and the
compressed zero-profile common-span route.

This is the non-cardinality version of the corrected P-window cover: active
profiles are still supplied by `CookLevinActiveProfileTypeCaseBlockers`, while
the all-zero profile is supplied directly by
`CookLevinZeroHistogramShiftCommonSpan`. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroProfileCommonSpan_deltaEqRateKappa
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
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
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
    (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
      M n hn2 htb hns hn4 hzero hactive)
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

/-- Concrete-NP prepended finite-row Route B certificate from the map-preimage
SPDP surface, with the corrected P-window inputs discharged from the primitive
per-type spanning package and the zero-profile support-card finite-sum side
condition.

This is the map-preimage analogue of the row-closure/unprojected-preimage
wrapper below.  It keeps the SPDP side on the weaker image-preimage surface
that `RouteBRicherGaugeSPDPSubspaceContainment` actually needs. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
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
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan
  have hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n) := by
    simpa [cookLevinZeroProfileNonScalarCardBound] using
      cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
        M n hn2 htb hns hzero
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4
      alpha beta alpha0 kappa gadgetN G chi Phi
      tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      hbound hactive preimage

/-- Concrete-NP prepended finite-row Route B certificate from the map-preimage
SPDP surface, with active profiles discharged from per-type spanning and the
zero profile supplied by an actual compressed common-span witness.

This avoids the support-cardinality side condition: the zero-profile input is
the exact `CookLevinZeroHistogramShiftCommonSpan` package isolated by the
profile-compression layer. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
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
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroProfileCommonSpan_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hzero
    (cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan)
    preimage
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
head/tail row-closure package, kernel/complement compatibility, and an
endpoint/charged P-window bridge.

This is the commutation-side sibling of the unprojected-preimage wrapper above:
finite-row closure plus kernel compatibility gives the map-preimage SPDP
surface, while the P-window side remains on the corrected charged endpoint
route. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_endpointChargedBridge_deltaEqRateKappa
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
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
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
    (routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_kernelCompatibility
      M n hn2 htb hns tail pkg hker)
    bridge

/-- Concrete-NP prepended finite-row Route B certificate from the explicit
head/tail row-closure package, kernel/complement compatibility, and the
corrected active-blocker/non-scalar P-window route.

The exposed assumptions are the corrected closure obligations: endpoint
charged local closure, non-scalar zero-profile budget, active live-profile
blockers, and finite-row closure/kernel compatibility. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_activeBlockersZeroNonScalar_deltaEqRateKappa
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
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    pkg hker
    (routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarCardBound
      M n hn2 htb hns hn4 charge hI1 hI2c hI3 hbound hactive)

/-- Concrete-NP prepended finite-row Route B certificate from the explicit
head/tail row-closure package and kernel/complement compatibility, with the
P-window inputs discharged from the primitive per-type spanning package and
the non-scalar zero-profile support-card side condition.

This is the kernel-compatible sibling of
`routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa`:
it keeps the SPDP side on finite-row closure plus kernel compatibility, while
the P-window side is reduced to the profile-compression/per-type spanning and
non-scalar zero-profile budget surfaces. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
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
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan
  have hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n) := by
    simpa [cookLevinZeroProfileNonScalarCardBound] using
      cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
        M n hn2 htb hns hzero
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4
      alpha beta alpha0 kappa gadgetN G chi Phi
      tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      hbound hactive
      (routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_kernelCompatibility
        M n hn2 htb hns tail pkg hker)

/-- Concrete-NP prepended finite-row Route B certificate from row closure and
kernel/complement compatibility, with the P-window side reduced to per-type
spanning plus an actual zero-profile common-span witness.

This is the paper-faithful compressed-span sibling of the support-card wrapper
above.  It does not assume the support-card finite sum fits inside the
within-profile budget. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
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
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    W hW_fin hW_dim hSpan hzero
    (routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_kernelCompatibility
      M n hn2 htb hns tail pkg hker)

/-- Endpoint/charged version of the preceding kernel-compatible wrapper.

Universal I1/I3 packages discharge the endpoint product/mlProj pieces, while
the charged-shift relation remains explicit as the corrected local closure
obligation.  The active-profile and zero-profile P-window assumptions are
again reduced to per-type/profile-compression spanning plus the non-scalar
support-card side condition. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_universalI13_chargedShift_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
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
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan
  have hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n) := by
    simpa [cookLevinZeroProfileNonScalarCardBound] using
      cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
        M n hn2 htb hns hzero
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_activeBlockersZeroNonScalar_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4 charge
      alpha beta alpha0 kappa gadgetN G chi Phi
      tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      (hI1_univ n (endpointAugmentedConcreteW n hn4))
      hI2c
      (hI3_univ n (endpointAugmentedConcreteW n hn4))
      hbound hactive pkg hker

/-- Endpoint/charged kernel-compatible wrapper using the compressed
zero-profile common-span witness directly.

Universal I1/I3 still discharge the endpoint product/mlProj pieces, charged
shift remains the corrected endpoint obligation, active profiles come from
per-type spanning, and the all-zero profile is the named common-span package
rather than a support-card side condition. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_universalI13_chargedShift_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
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
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_endpointChargedBridge_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4 charge
      alpha beta alpha0 kappa gadgetN G chi Phi
      tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      pkg hker
      (routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroProfileCommonSpan
        M n hn2 htb hns hn4 charge
        (hI1_univ n (endpointAugmentedConcreteW n hn4))
        hI2c
        (hI3_univ n (endpointAugmentedConcreteW n hn4))
        hzero hactive)

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

/-- Concrete-NP prepended finite-row Route B certificate with the corrected
P-window inputs discharged from the primitive per-type spanning package and
the non-scalar zero-profile support-card side condition.

This keeps the final SPDP work on the concrete finite-row gauge obligations
(`pkg` and `unprojectedPreimage`) while replacing the exposed P-window inputs
`CookLevinActiveProfileTypeCaseBlockers` and
`cookLevinZeroProfileNonScalarCardBound ≤ withinProfileBound` by the smaller
mathematical packages that currently imply them. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
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
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (unprojectedPreimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan
  have hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n) := by
    simpa [cookLevinZeroProfileNonScalarCardBound] using
      cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
        M n hn2 htb hns hzero
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4
      alpha beta alpha0 kappa gadgetN G chi Phi
      tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      hbound hactive pkg unprojectedPreimage

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroProfileCommonSpan_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_activeBlockersZeroNonScalar_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_universalI13_chargedShift_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_kernelCompatibility_universalI13_chargedShift_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa

end PallLean.Paper93.Paper283

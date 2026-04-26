import PallLean.Paper93.Paper283.RouteBRicherGaugeFiniteRowsSPDPCommutationBridge
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteWChargedClosure
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure

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

/-- Corrected finite-row Route B assembly using only the P-window cover data
that the final certificate actually consumes.

Compared with
`routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_activeBlockersZeroNonScalar_deltaEqRateKappa`,
this theorem avoids asking for endpoint/charged local-closure inputs.  Those
are useful diagnostics for the corrected profile route, but the certificate
only needs the unprojected P-window finite-span cover. -/
theorem routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_activeBlockersZeroNonScalarCover_deltaEqRateKappa
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
  routeBPerInstanceCertificate_of_finiteRowsSPDPGeneralCommutation_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hcomm
    (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarCardBound
      M n hn2 htb hns hn4 hbound hactive)
    Q i hrow hextract hsource

/-- ConcreteW row embeddings close the active-blocker input of the corrected
Route B P-window bridge, while the finite support-card side condition closes
the literal non-scalar zero-profile cardinality input.

This is only a reduction: the remaining arithmetic/combinatorial statement is
`CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns`. -/
theorem routeB_activeBlockersZeroNonScalarInputs_of_concreteW_zeroSupportCardSum
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns) :
    CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns ∧
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n) := by
  refine ⟨?_, ?_⟩
  · exact
      cookLevinActiveProfileTypeCaseBlockers_closed_by_concreteW
        M n hn2 htb hns hn4 hRowEmbeddings
  · simpa [cookLevinZeroProfileNonScalarCardBound] using
      cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
        M n hn2 htb hns hzero

/-- External-base-cardinality version of
`routeB_activeBlockersZeroNonScalarInputs_of_concreteW_zeroSupportCardSum`.

This is only a reduction: the remaining arithmetic/combinatorial statement is
`CookLevinZeroProfileSupportBaseCardSideCondition M n hn2 htb hns b`. -/
theorem routeB_activeBlockersZeroNonScalarInputs_of_concreteW_zeroSupportBaseCard
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (b : Nat)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hzero :
      CookLevinZeroProfileSupportBaseCardSideCondition M n hn2 htb hns b) :
    CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns ∧
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n) := by
  refine ⟨?_, ?_⟩
  · exact
      cookLevinActiveProfileTypeCaseBlockers_closed_by_concreteW
        M n hn2 htb hns hn4 hRowEmbeddings
  · simpa [cookLevinZeroProfileNonScalarCardBound] using
      cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
        M n hn2 htb hns b hzero

/-- Row embeddings close the active live-profile blockers, and the exact
zero-profile support-card side condition closes the non-scalar cardinality
bound.  This is the current tightest corrected P-window input surface. -/
theorem routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_rowEmbeddingsZeroSupport_deltaEqRateKappa
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
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
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
  by
    rcases
      routeB_activeBlockersZeroNonScalarInputs_of_concreteW_zeroSupportCardSum
        M n hn2 htb hns hn4 hRowEmbeddings hzero with
      ⟨hactive, hbound⟩
    exact
      routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_activeBlockersZeroNonScalarCover_deltaEqRateKappa
        (N := N) (d := d)
        M n hn2 htb hns hn4 alpha beta alpha0 kappa gadgetN G chi Phi
        rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
        hbound hactive hcomm Q i hrow hextract hsource

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_activeBlockersZeroNonScalar_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_activeBlockersZeroNonScalarCover_deltaEqRateKappa
#print axioms routeB_activeBlockersZeroNonScalarInputs_of_concreteW_zeroSupportCardSum
#print axioms routeB_activeBlockersZeroNonScalarInputs_of_concreteW_zeroSupportBaseCard
#print axioms routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_rowEmbeddingsZeroSupport_deltaEqRateKappa

end PallLean.Paper93.Paper283

import PallLean.Paper93.Paper283.RouteBRicherGaugeCorrectedAssembly
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteNP

/-!
# Corrected Route B assembly with concrete NP finite-row data

This file closes the NP-side inputs for the corrected finite-row Route B
assembly by prepending the concrete Cook-Levin identity-minor source row to an
otherwise arbitrary richer finite-row gauge.
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

/-- Add the concrete Cook-Levin NP source row as row `0`, keeping the
remaining richer rows as the tail. -/
noncomputable def routeBRicherConcreteNPPrependedRows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Fin (m + 1) -> SATDeciderGaugeSpace M n hn2 htb hns :=
  Fin.cases (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) tail

/-- The prepended row is the concrete embedded NP source witness. -/
theorem routeBRicherConcreteNPPrependedRows_zero_eq_embed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail 0 =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns) := by
  rw [routeBRicherConcreteNPPrependedRows]
  exact routeBRicherConcreteNPWitnessRows_eq_embed M n hn2 htb hns 0

/-- For any finite-row gauge, once the NP source is chosen to be the concrete
Cook-Levin witness, the extraction equality follows from `embed = compiled`. -/
theorem routeBRicherConcreteNP_extracts_compiled_for_rows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns)
          (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) := by
  rw [routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly]

/-- Corrected finite-row Route B assembly with the NP row data made concrete
by prepending the Cook-Levin identity-minor row. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
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
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)))
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hcomm bridge
    (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
    0
    (routeBRicherConcreteNPPrependedRows_zero_eq_embed
      M n hn2 htb hns tail)
    (routeBRicherConcreteNP_extracts_compiled_for_rows
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
      M n hn hn2 htb hns)

/-- Corrected finite-row Route B assembly with concrete NP data and the
active-blocker/zero-profile non-scalar P-window reduction. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_activeBlockersZeroNonScalar_deltaEqRateKappa
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
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hcomm
    (routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarCardBound
      M n hn2 htb hns hn4 charge hI1 hI2c hI3 hbound hactive)

/-- Corrected concrete-NP Route B assembly using endpoint/charged local
closure and a genuine zero-profile common-span witness.

This is the concrete-head version of the compressed-zero-profile final
surface: `hzero` supplies the zero-profile span directly, while `hcomm`
supplies the finite-row projection transport. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_endpointChargedZeroProfileCommonSpan_deltaEqRateKappa
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
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hcomm
    { localClosure :=
        endpointAugmentedConcreteW_correctedLocalClosure_of_charged_components
          n hn4 charge hI1 hI2c hI3
      cover :=
        routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
          M n hn2 htb hns hn4 hzero hactive }

/-- Stronger corrected reduction with concrete NP data: concreteW row
embeddings close the active live-profile blockers, the zero-profile support
side condition closes the non-scalar cardinality bound, and the prepended row
closes the NP identity-minor fields. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_rowEmbeddingsZeroSupport_deltaEqRateKappa
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
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsGeneralCommutation_rowEmbeddingsZeroSupport_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hRowEmbeddings hzero hcomm
    (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
    0
    (routeBRicherConcreteNPPrependedRows_zero_eq_embed
      M n hn2 htb hns tail)
    (routeBRicherConcreteNP_extracts_compiled_for_rows
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
      M n hn hn2 htb hns)

/-- Concrete NP-row corrected Route B assembly with the SPDP side reduced to
map-preimage and the P-window side closed from concreteW row embeddings.

This is the tightest concrete finite-row surface in this file: the concrete
Cook-Levin identity-minor row supplies the NP data, `preimage` supplies exactly
the SPDP image-containment witness, and concreteW row embeddings supply the
P-window cover without the separate zero-profile support-card side
condition. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_rowEmbeddings_deltaEqRateKappa
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
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_rowEmbeddings_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    preimage hRowEmbeddings
    (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
    0
    (routeBRicherConcreteNPPrependedRows_zero_eq_embed
      M n hn2 htb hns tail)
    (routeBRicherConcreteNP_extracts_compiled_for_rows
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
      M n hn hn2 htb hns)

/-- Concrete NP-row corrected Route B assembly with finite-row commutation
converted through the weaker map-preimage SPDP surface.

This is the shortest corrected path from a finite-row generator commutation
proof to the concrete NP Route B certificate: commutation is used only to
produce `RouteBRicherGaugeFiniteRowsSPDPMapPreimage`, and the P-window side
is supplied by the existing concreteW row-embedding cover. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_rowEmbeddings_deltaEqRateKappa
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
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)))
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_rowEmbeddings_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorCommutation
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
      hcomm)
    hRowEmbeddings

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedRows_zero_eq_embed
#print axioms routeBRicherConcreteNP_extracts_compiled_for_rows
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_activeBlockersZeroNonScalar_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_endpointChargedZeroProfileCommonSpan_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_rowEmbeddingsZeroSupport_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_rowEmbeddings_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsGeneralCommutation_rowEmbeddings_deltaEqRateKappa

end PallLean.Paper93.Paper283

import PallLean.Paper93.Paper283.RouteBHardMathFrontierProgress

/-!
# Route B explicit-complement projection assembly

This file packages the Route B projection-policy boundary for an explicit
complement.  The direct SPDP preimage statement below uses the supplied
explicit-complement projection.  The existing downstream Route B certificate
wrappers still consume the selected finite-row projection, so the certificate
wrappers in this file cross that boundary only under the checked equality
criterion
`RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Explicit-complement SPDP map-preimage surface for the concrete
multilinear-tail projection.

This is the direct map-preimage statement for the supplied complement policy,
not for the arbitrary selected finite-row projection. -/
structure RouteBRicherConcreteNPPrependedMultilinearProjectionWithComplementSPDPMapPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    Prop where
  map_preimage :
    forall (spdpKappa ell : Nat)
      (p : SATDeciderGaugeSpace M n hn2 htb hns)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      ∃ raw : SATDeciderGaugeSpace M n hn2 htb hns,
        raw ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            spdpKappa ell p
        ∧
        routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
            M n hn2 htb hns C hC raw =
          routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
              M n hn2 htb hns C hC p)
            S shift

/-- Explicit-complement descent gives the direct explicit-complement SPDP
map-preimage witness by taking the unprojected generator row as the raw
preimage. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_projectionWithComplementDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionWithComplementSPDPMapPreimage
        M n hn2 htb hns C hC := by
  constructor
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  refine
    ⟨routeBSPDPGeneratorRow M n hn2 htb hns p S shift, ?_, ?_⟩
  · exact
      Submodule.subset_span
        ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · exact
      (hdesc spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm).symm

/-- Checked reduction from explicit-complement descent to the selected
finite-row map-preimage surface consumed by existing Route B wrappers.

The reduction requires equality of the explicit-complement projection map and
the selected projection map; no equality is claimed for an arbitrary
complement policy. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionWithComplementDescent_of_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionDescent
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_projectionWithComplementDescent_of_realizesSelectedProjection
      M n hn2 htb hns C hC hpolicy hdesc)

/-- Checked reduction from explicit-complement descent to the selected
finite-row SPDP image-containment field. -/
theorem routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_projectionWithComplementDescent_of_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_projectionDescent
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_projectionWithComplementDescent_of_realizesSelectedProjection
      M n hn2 htb hns C hC hpolicy hdesc)

/-- Concrete-tail Route B certificate from explicit-complement descent, after
checking that the explicit-complement projection realizes the selected
finite-row projection. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_perTypeSpanning_zeroSupportCardSum_realizesSelectedProjection_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (W :
      SymmetricPowerBound.ConstraintType ->
        Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    W hW_fin hW_dim hSpan hzero
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionWithComplementDescent_of_realizesSelectedProjection
      M n hn2 htb hns C hC hpolicy hdesc)

/-- Concrete-tail Route B certificate from explicit-complement descent and a
zero-profile common-span witness, after the same checked selected-projection
reduction. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_perTypeSpanning_zeroProfileCommonSpan_realizesSelectedProjection_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (W :
      SymmetricPowerBound.ConstraintType ->
        Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroProfileCommonSpan_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    W hW_fin hW_dim hSpan hzero
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionWithComplementDescent_of_realizesSelectedProjection
      M n hn2 htb hns C hC hpolicy hdesc)

/-- Endpoint-bridge Route B assembly from explicit-complement descent, with
the selected finite-row projection used downstream only after the checked
policy-realization criterion. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_endpointChargedBridge_realizesSelectedProjection_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionWithComplementDescent_of_realizesSelectedProjection
      M n hn2 htb hns C hC hpolicy hdesc)
    bridge

/-- Narrowed hard-math frontier assembly from explicit-complement descent.

The explicit complement is not identified with the selected projection unless
`hpolicy` proves the projection maps are equal.  Under that checked reduction,
explicit-complement descent gives the selected kernel-generator condition
consumed by the current hard-math frontier theorem. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_realizesSelectedProjection_canonicalResidual_compressedFinrank_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hCanon : ConcreteWChargedShiftClosure n hn4 charge)
    (hResidual :
      EndpointAugmentedConcreteWChargedShiftResidualClosure n hn4 charge)
    (W :
      SymmetricPowerBound.ConstraintType ->
        Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hcompressed :
      CookLevinZeroProfileCompressedSpanFinrankCondition M n hn2 htb hns)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hselected :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns :=
    routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_projectionWithComplementDescent_of_realizesSelectedProjection
      M n hn2 htb hns C hC hpolicy hdesc
  have hkernel :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns :=
    (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
      M n hn2 htb hns).mp hselected
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_kernelGeneratorZero_canonicalResidual_compressedFinrank_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4 charge
      alpha beta alpha0 kappa gadgetN G chi Phi
      hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      hI1_univ hI3_univ hCanon hResidual
      W hW_fin hW_dim hSpan hcompressed hkernel

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherConcreteNPPrependedMultilinearProjectionWithComplementSPDPMapPreimage
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_projectionWithComplementDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionWithComplementDescent_of_realizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_projectionWithComplementDescent_of_realizesSelectedProjection
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_perTypeSpanning_zeroSupportCardSum_realizesSelectedProjection_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_perTypeSpanning_zeroProfileCommonSpan_realizesSelectedProjection_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_endpointChargedBridge_realizesSelectedProjection_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_realizesSelectedProjection_canonicalResidual_compressedFinrank_deltaEqRateKappa

end PallLean.Paper93.Paper283

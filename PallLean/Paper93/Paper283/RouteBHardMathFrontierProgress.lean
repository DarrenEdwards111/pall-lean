import PallLean.Paper93.DeepMath.PathB.ZeroProfileCompressedSpanProgress
import PallLean.Paper93.Paper283.RouteBChargedShiftClosureProgress
import PallLean.Paper93.Paper283.RouteBProjectionDescentProgress

/-!
# Route B hard-math frontier progress

This file composes the three current paper-faithful hard-math surfaces:

* charged endpoint shift closure is reduced to canonical charged closure plus
  the endpoint-extra residual split;
* the zero-profile common span is supplied by the sharp compressed-span
  finrank condition;
* the multilinear-tail projection side is stated as kernel-generator
  annihilation for the selected finite-row projection.

No surface below asserts those inputs.  The point is to make the corrected
Route B certificate consume exactly these narrowed obligations.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Concrete multilinear-tail Route B certificate from the narrowed hard-math
frontier.

The assumptions are the corrected Route B obligations, with the previous
zero-profile common-span package replaced by its compressed finrank form and
the endpoint charged shift closure replaced by canonical charged closure plus
the explicit endpoint residual split.  The SPDP side uses the selected
multilinear-tail projection through kernel-generator annihilation, which is
equivalent to projection descent by `RouteBProjectionDescentProgress`.
-/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_kernelGeneratorZero_canonicalResidual_compressedFinrank_deltaEqRateKappa
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
    (hkernel :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge :=
    endpointAugmentedConcreteW_chargedShiftClosure_of_canonical_and_residual
      n hn4 charge hCanon hResidual
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan
  have hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns :=
    cookLevinZeroHistogramShiftCommonSpan_of_compressedSpanFinrankCondition
      M n hn2 htb hns hcompressed
  have hbridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge :=
    routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroProfileCommonSpan
      M n hn2 htb hns hn4 charge
      (hI1_univ n (endpointAugmentedConcreteW n hn4))
      hI2c
      (hI3_univ n (endpointAugmentedConcreteW n hn4))
      hzero hactive
  have hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns :=
    (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
      M n hn2 htb hns).mpr hkernel
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_endpointChargedBridge_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4 charge
      alpha beta alpha0 kappa gadgetN G chi Phi
      (routeBRicherMultilinearTailRows M n hn2 htb hns)
      hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionDescent
        M n hn2 htb hns hdesc)
      hbridge

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_kernelGeneratorZero_canonicalResidual_compressedFinrank_deltaEqRateKappa

end PallLean.Paper93.Paper283

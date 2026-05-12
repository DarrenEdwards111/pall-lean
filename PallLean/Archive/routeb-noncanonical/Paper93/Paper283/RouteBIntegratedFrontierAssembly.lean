import PallLean.Paper93.DeepMath.PathB.ActiveProfileBlockerConcreteProgress
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress
import PallLean.Paper93.DeepMath.PathB.ZeroProfileQuotientTypeCompression
import PallLean.Paper93.Paper283.RouteBEndpointChargeSemanticsProgress
import PallLean.Paper93.Paper283.RouteBExplicitComplementProjectionAssembly
import PallLean.Paper93.Paper283.RouteBExplicitComplementProjectionPolicyProgress

/-!
# Route B integrated frontier assembly

This file composes the current paper-faithful Route B frontiers without
closing any of them by fiat:

* zero-profile rows are supplied by the quotient/type certificate plus an
  explicitly paid projection residual;
* active profiles are supplied by the concreteW active-profile closure
  frontier;
* endpoint closure is supplied by `PaperEndpointChargeSemantics`;
* the projection route uses an explicit complement only after the checked
  selected-projection realization criterion.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MvPolynomial
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Full current Route B frontier wrapper.

The theorem intentionally still exposes the four hard frontiers as hypotheses:
the quotient zero-profile certificate/residual budget, concreteW active-profile
closure, endpoint charge semantics, and explicit-complement projection descent
plus selected-projection realization. -/
theorem routeBPerInstanceCertificate_of_endpointSemantic_zeroQuotient_activeConcreteW_projectionWithComplement
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
    (hSem : PaperEndpointChargeSemantics n hn4 charge)
    (hI1 :
      PallLean.Paper93.Closure.PerTypeProductGrouping
        (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PallLean.Paper93.Closure.PerTypeMlprojClosure
        (n := n) (endpointAugmentedConcreteW n hn4))
    {typeBudget residualBudget : Nat}
    (cert :
      ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget)
    (hresidual :
      CookLevinZeroProfileProjectionResidualClosureWithBudget
        M n hn2 htb hns cert.project residualBudget)
    (hbudget :
      typeBudget + residualBudget <= withinProfileBound (Nat.log 2 n))
    (hactiveFrontier :
      CookLevinActiveProfileConcreteWObligation M n hn2 htb hns hn4)
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
  have hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns :=
    cookLevinZeroHistogramShiftCommonSpan_of_quotientTypeCertificate_residualClosure
      M n hn2 htb hns cert hresidual hbudget
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_activeConcreteWObligation
      M n hn2 htb hns hn4 hactiveFrontier
  let bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge :=
    routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroProfileCommonSpan
      M n hn2 htb hns hn4 charge hSem hI1 hI3 hzero hactive
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_endpointChargedBridge_realizesSelectedProjection_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4 charge
      alpha beta alpha0 kappa gadgetN G chi Phi
      hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      bridge C hC hpolicy hdesc

/-- Concrete-endpoint specialization of the integrated Route B frontier.

This removes the endpoint semantic hypothesis when the intended charge is the
checked concrete endpoint-span one-step charge. -/
theorem routeBPerInstanceCertificate_of_concreteEndpoint_zeroQuotient_activeConcreteW_projectionWithComplement
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
    (hI1 :
      PallLean.Paper93.Closure.PerTypeProductGrouping
        (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PallLean.Paper93.Closure.PerTypeMlprojClosure
        (n := n) (endpointAugmentedConcreteW n hn4))
    {typeBudget residualBudget : Nat}
    (cert :
      ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget)
    (hresidual :
      CookLevinZeroProfileProjectionResidualClosureWithBudget
        M n hn2 htb hns cert.project residualBudget)
    (hbudget :
      typeBudget + residualBudget <= withinProfileBound (Nat.log 2 n))
    (hactiveFrontier :
      CookLevinActiveProfileConcreteWObligation M n hn2 htb hns hn4)
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
  routeBPerInstanceCertificate_of_endpointSemantic_zeroQuotient_activeConcreteW_projectionWithComplement
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    (concreteWEndpointSpanOneStepCharge n hn4)
    alpha beta alpha0 kappa gadgetN G chi Phi
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (concreteWEndpointSpanOneStepCharge_paperEndpointChargeSemantics n hn4)
    hI1 hI3 cert hresidual hbudget hactiveFrontier C hC hpolicy hdesc

/-- Integrated Route B wrapper using the sharper projected normal-form
zero-profile certificate.

Compared with
`routeBPerInstanceCertificate_of_endpointSemantic_zeroQuotient_activeConcreteW_projectionWithComplement`,
the zero-profile side now pays the summed symmetric-profile normal-form budget
from `ZeroProfileProjectedNormalFormCertificate`, plus the explicit projection
residual. -/
theorem routeBPerInstanceCertificate_of_endpointSemantic_zeroNormalForm_activeConcreteW_projectionWithComplement
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
    (hSem : PaperEndpointChargeSemantics n hn4 charge)
    (hI1 :
      PallLean.Paper93.Closure.PerTypeProductGrouping
        (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PallLean.Paper93.Closure.PerTypeMlprojClosure
        (n := n) (endpointAugmentedConcreteW n hn4))
    {typeBudget residualBudget : Nat}
    (cert :
      ZeroProfileProjectedNormalFormCertificate (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget)
    (hresidual :
      CookLevinZeroProfileProjectionResidualClosureWithBudget
        M n hn2 htb hns cert.project residualBudget)
    (hbudget :
      typeBudget + residualBudget <= withinProfileBound (Nat.log 2 n))
    (hactiveFrontier :
      CookLevinActiveProfileConcreteWObligation M n hn2 htb hns hn4)
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
  have hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns :=
    cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_residualClosure
      M n hn2 htb hns cert hresidual hbudget
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_activeConcreteWObligation
      M n hn2 htb hns hn4 hactiveFrontier
  let bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge :=
    routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroProfileCommonSpan
      M n hn2 htb hns hn4 charge hSem hI1 hI3 hzero hactive
  exact
    routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_projectionWithComplementDescent_endpointChargedBridge_realizesSelectedProjection_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns hn4 charge
      alpha beta alpha0 kappa gadgetN G chi Phi
      hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      bridge C hC hpolicy hdesc

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_endpointSemantic_zeroQuotient_activeConcreteW_projectionWithComplement
#print axioms routeBPerInstanceCertificate_of_concreteEndpoint_zeroQuotient_activeConcreteW_projectionWithComplement
#print axioms routeBPerInstanceCertificate_of_endpointSemantic_zeroNormalForm_activeConcreteW_projectionWithComplement

end PallLean.Paper93.Paper283

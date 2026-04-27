import PallLean.Paper93.Paper283.RouteBRicherGaugePrependedCorrectedMapPreimage
import PallLean.Paper93.DeepMath.PathB.ActiveProfileEndpointAugmentedProgress
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress

/-!
# Paper-faithful Route B integration

This file connects the recently corrected PathB proof objects to the concrete
Route B assembly surface:

* zero profile: Boolean-normalized normal forms plus a paid residual span;
* active profiles: endpoint-augmented profile-local frontiers;
* projection side: the finite-row map-preimage route from the concrete
  prepended Cook-Levin row package.

It deliberately avoids the older raw support-count and singleton-killing
projection routes.
-/

namespace PallLean.Paper93.Paper283

open TuringMachine
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Concrete prepended-row Route B assembly from the corrected paper-faithful
P-side objects:

* active profiles are discharged by the endpoint-augmented active frontier;
* zero profile is discharged by Boolean-normalized normal forms; the Boolean
  normalizer fixes the existing `mlProj` shifted rows, so no singleton-killing
  residual is required here;
* the SPDP side uses the concrete finite-row closure package and kernel
  compatibility to obtain the map-preimage surface.

This is the downstream connection from the Boolean/profile compression work
into `RouteBPerInstanceCertificate`; the remaining assumptions are exactly the
Boolean row classifier/type budget, active frontier, and finite-row
map-preimage obligations. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_kernelCompatibility_endpointActive_booleanZeroNormalForms_deltaEqRateKappa
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
    {typeBudget : Nat}
    (hzeroNormalForms :
      CookLevinZeroProfileBooleanNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hzeroBudget :
      typeBudget <= withinProfileBound (Nat.log 2 n))
    (hactiveFrontier :
      EndpointAugmentedActiveProfileFrontier M n hn2 htb hns hn4)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns :=
    cookLevinZeroHistogramShiftCommonSpan_of_booleanNormalFormObligation
      M n hn2 htb hns hzeroNormalForms hzeroBudget
  have hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns :=
    cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileFrontier
      M n hn2 htb hns hn4 hactiveFrontier
  exact
    routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_activeBlockersZeroProfileCommonSpan_deltaEqRateKappa
      (N := N) (d := d)
      M n hn2 htb hns hn4
      alpha beta alpha0 kappa gadgetN G chi Phi
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
      hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      hzero hactive
      (routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_kernelCompatibility
        M n hn2 htb hns tail pkg hker)
      (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
      0
      (routeBRicherConcreteNPPrependedRows_zero_eq_embed
        M n hn2 htb hns tail)
      (routeBRicherConcreteNP_extracts_compiled_for_rows
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
      (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
        M n hn hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_kernelCompatibility_endpointActive_booleanZeroNormalForms_deltaEqRateKappa

end PallLean.Paper93.Paper283

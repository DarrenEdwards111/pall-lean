import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteDelta
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteScalarClosure
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowConcreteCover

/-!
# Named final frontier for the concrete Route B richer gauge

This file removes the last scalar/log-det side condition from the concrete
Route B frontier and states the remaining obligations only through the named
polynomial/profile packages.

The analytic Bridge A budget is now fixed by the concrete delta schedule from
`RouteBRicherGaugeConcreteDelta`.  The remaining assumptions are exactly:

* scalar closure of the concrete Cook-Levin witness row;
* unprojected SPDP-preimage closure for the richer projection;
* the P-window fixed-profile common-span family.
-/

namespace PallLean.Paper93.Paper283

open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Concrete Route B per-instance certificate from the named SPDP/P-window
frontier obligations, with the analytic delta side condition already closed by
the explicit log-divided rank schedule.

After this theorem, the remaining load-bearing inputs are no longer scalar
budget arithmetic or anonymous quantified transport facts.  They are the two
named SPDP closure packages plus the fixed-profile P-window common-span
family. -/
theorem routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hscalar :
      RouteBRicherConcreteNPCompiledPolyScalarRowClosure
        M n hn2 htb hns)
    (hunprojected :
      RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
        M n hn2 htb hns)
    (hpwindow :
      forall h : ProfileHistogram,
        CookLevinAllBoundedProfileCommonSpanAtProfile
          M n hn2 htb hns h) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns
      alpha beta alpha0 kappa gadgetN G chi Phi
      (eta := eta) (theta := theta)
      hN heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure
        M n hn2 htb hns hscalar hunprojected)
      (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpanAtProfiles
        M n hn2 htb hns hpwindow)

/-- Same named final frontier, but consuming the all-profile
template-collapse lemma directly for the P-window side. -/
theorem routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_templateCollapse_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hscalar :
      RouteBRicherConcreteNPCompiledPolyScalarRowClosure
        M n hn2 htb hns)
    (hunprojected :
      RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
        M n hn2 htb hns)
    (hcollapse :
      CookLevinProfileTemplateCollapseLemma M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns
      alpha beta alpha0 kappa gadgetN G chi Phi
      (eta := eta) (theta := theta)
      hN heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure
        M n hn2 htb hns hscalar hunprojected)
      (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_templateCollapse
        M n hn2 htb hns hcollapse)

/-- Named final frontier through the non-template P-side route.  This is the
route that survives the zero-profile no-go: active/live profiles are handled
separately from a non-scalar zero-histogram common-span certificate. -/
theorem routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_liveProfiles_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hscalar :
      RouteBRicherConcreteNPCompiledPolyScalarRowClosure
        M n hn2 htb hns)
    (hunprojected :
      RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
        M n hn2 htb hns)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hlive :
      CookLevinAllBoundedProfileCommonSpanLiveProfileCases
        M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns
      alpha beta alpha0 kappa gadgetN G chi Phi
      (eta := eta) (theta := theta)
      hN heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure
        M n hn2 htb hns hscalar hunprojected)
      (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_liveProfileCases
        M n hn2 htb hns hn4 hzero hlive)

/-- ConcreteW row-embedding closure is the current strongest exposed route
into the P-window cover.  This wrapper records the exact final surface when
that direct profile-span package is supplied. -/
theorem routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_concreteW_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hscalar :
      RouteBRicherConcreteNPCompiledPolyScalarRowClosure
        M n hn2 htb hns)
    (hunprojected :
      RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
        M n hn2 htb hns)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_deltaEqRateKappa
      (N := N) (d := d)
      M n hn hn2 htb hns
      alpha beta alpha0 kappa gadgetN G chi Phi
      (eta := eta) (theta := theta)
      hN heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure
        M n hn2 htb hns hscalar hunprojected)
      (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_rowEmbeddings
        M n hn2 htb hns hn4 hRowEmbeddings)

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_templateCollapse_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_liveProfiles_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_namedRicherGaugeFrontier_concreteW_deltaEqRateKappa

end PallLean.Paper93.Paper283

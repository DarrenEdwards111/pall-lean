import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteAssembly
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteCoefficients
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowConcreteCover

/-!
# Route B richer-gauge final frontier

This file is the current integration frontier for the concrete Route B
richer finite-row gauge.  It consumes the checked concrete assembly, the
one-row SPDP scalar-closure reduction, and the concrete P-window cover route.

After the concrete matrix/NP/rank data and the log-div Bridge A budget are
specialized, the only remaining inputs are the genuinely polynomial facts:

* the single concrete witness row is closed under every admissible SPDP
  generator up to a scalar;
* the same projected generators lie in the unprojected blocked SPDP subspace;
* the fixed-profile common-span certificates feeding the P-window cover.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open TuringMachine
open WithinProfileBound
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The concrete one-row scalar-closure frontier for Route B SPDP containment.

The finite-row span half is reduced to the scalar statement for the single
NP-witness row.  The unprojected SPDP-preimage half remains explicit because it
is not a finite-row coefficient fact. -/
theorem routeBRicherConcreteNPWitness_spdpSubspaceContainment_of_scalarClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hscalar :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        ∃ c : Rat,
          routeBSPDPGeneratorRow M n hn2 htb hns
              (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0)
              S shift =
            c • routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0)
    (hunprojected :
      forall (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
                (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)
            S shift
          ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            spdpKappa ell p) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) := by
  apply
    routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_rowClosure
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
  · intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm i
    fin_cases i
    exact
      (mem_finiteRowsSubmodule_one_iff_exists_scalar
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0)
          S shift)).mpr
        (hscalar spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm)
  · exact hunprojected

/-- Final concrete Route B frontier under the log-div Bridge A schedule.

This theorem exposes only the final scalar/arithmetic side condition
`hdelta_rate`, the one-row SPDP polynomial facts, and the pointwise
fixed-profile common-span certificates used by the concrete P-window cover
route. -/
theorem routeBPerInstanceCertificate_of_richerGaugeFinalFrontier_logDivBudget
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta delta : Real}
    (hN : 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hdelta_rate :
      delta <=
        (Real.log (1 + theta * eta) /
            ((pocketFamily alpha kappa gadgetN).rank : Real)) *
          (kappa : Real))
    (hscalar :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        ∃ c : Rat,
          routeBSPDPGeneratorRow M n hn2 htb hns
              (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0)
              S shift =
            c • routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0)
    (hunprojected :
      forall (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
                (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)
            S shift
          ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            spdpKappa ell p)
    (hpwindow :
      forall h : SymmetricPowerBound.ProfileHistogram,
        CookLevinAllBoundedProfileCommonSpanAtProfile M n hn2 htb hns h) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_logDivBudget
    (N := N) (d := d)
    M n hn hn2 htb hns
    alpha beta alpha0 kappa gadgetN G chi Phi
    hN heta htheta halpha halpha0 hkappa hgadgetN hdelta_rate
    (routeBRicherConcreteNPWitness_spdpSubspaceContainment_of_scalarClosure
      M n hn2 htb hns hscalar hunprojected)
    (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpanAtProfiles
      M n hn2 htb hns hpwindow)

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPWitness_spdpSubspaceContainment_of_scalarClosure
#print axioms routeBPerInstanceCertificate_of_richerGaugeFinalFrontier_logDivBudget

end PallLean.Paper93.Paper283

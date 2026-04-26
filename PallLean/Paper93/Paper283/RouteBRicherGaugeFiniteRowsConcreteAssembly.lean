import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteDelta
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPContainmentFiniteSpan
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowConcreteDischarge

/-!
# Corrected finite-row concrete Route B assembly

The one-row concrete witness route is useful for the NP fixed-row check, but
it cannot supply the SPDP containment field by scalar closure: the repository
now proves that scalar closure is false.  This file exposes the corrected
surface for a genuinely richer finite-row gauge.

The selected row family is arbitrary and finite.  The concrete compiled-gadget
matrix, the log-divided Bridge A budget, the delta schedule, and the row-count
rank bound are all discharged here.  The remaining semantic inputs are:

* finite-row SPDP containment, or its explicit projected-generator linear
  combination criterion;
* a P-window finite-span cover;
* one row that preserves the NP identity-minor source witness.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- General finite-row concrete Route B assembly.

Compared with `RouteBRicherGaugeConcreteAssembly`, this theorem does not fix
the richer gauge to the impossible one-row scalar-closure candidate.  It
accepts any finite row family, proves the concrete compiled-gadget spectral
and row-count budget fields, and leaves the genuine finite-row transport data
explicit. -/
theorem routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
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
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
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
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  let rate :=
    routeBRicherGaugeConcreteRankLogRate alpha kappa gadgetN eta theta
  let delta :=
    routeBRicherGaugeConcreteDelta alpha kappa gadgetN eta theta
  have hlog_nonneg : 0 <= Real.log (1 + theta * eta) :=
    log_one_add_theta_mul_eta_nonneg htheta heta
  have hrank_pos_nat : 0 < (pocketFamily alpha kappa gadgetN).rank :=
    pocketFamily_rank_pos_of_kappa_pos alpha kappa gadgetN
      halpha hkappa hgadgetN
  have hrank_pos_real :
      0 < ((pocketFamily alpha kappa gadgetN).rank : Real) := by
    exact_mod_cast hrank_pos_nat
  have hrate_nonneg : 0 <= rate := by
    simp [rate, routeBRicherGaugeConcreteRankLogRate]
    exact div_nonneg hlog_nonneg hrank_pos_real.le
  have hdelta_rate : delta <= rate * (kappa : Real) := by
    simp [delta, rate, routeBRicherGaugeConcreteDelta,
      routeBRicherGaugeConcreteRankLogRate]
  have hbudget :
      rate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
            Real) <=
        ((Finset.univ : Finset (Fin N)).card : Real) *
          Real.log (1 + theta * eta) := by
    have hbudget' :=
      concreteBridgeA_spectral_budget_log_div_pocketRank
        alpha beta alpha0 kappa gadgetN G chi Phi
        halpha hkappa hgadgetN heta htheta
    simpa [rate, routeBRicherGaugeConcreteRankLogRate,
      cookLevinPocketLocalGadgetFamily, cookLevinPocketLocalGadget,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
      using hbudget'
  have hmatrixRank :
      (compiledGadget eta N).rank = N :=
    compiledGadget_rank_full eta N heta hN
  have hspanRank :
      (Module.finrank Rat (finiteRowsSubmodule rows) : Real) <=
        ((compiledGadget eta N).rank : Real) := by
    have hnat :
        Module.finrank Rat (finiteRowsSubmodule rows) <=
          (compiledGadget eta N).rank := by
      rw [hmatrixRank]
      exact le_trans (finiteRowsSubmodule_finrank_le_card rows) hrowCount
    exact_mod_cast hnat
  exact
    routeBPerInstanceCertificate_of_richerFiniteRows_eigenvalueFloor
      (N := N) (d := d)
      M n hn2 htb hns
      alpha beta alpha0 kappa gadgetN G chi Phi
      (theta := theta) (delta := delta)
      (rankLogRate := rate) (lambdaFloor := eta)
      (compiledGadget eta N)
      (compiledGadget_posSemidef_of_positive_coupling
        (N := N) eta heta)
      (Finset.univ : Finset (Fin N)) rows
      htheta halpha halpha0 hgadgetN hrate_nonneg hdelta_rate
      heta.le
      (by
        intro j _hj
        exact compiledGadget_eigenvalue_floor eta heta
          (compiledGadget_posSemidef_of_positive_coupling
            (N := N) eta heta) j)
      hbudget hspanRank hcontain cover Q i hrow hextract hsource

/-- Finite-row concrete assembly with SPDP containment supplied by the checked
linear-combination/preimage criterion for projected generators. -/
theorem routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_linearCombination_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
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
    (hgen :
      forall (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        ∃ coeff : Fin m -> Rat,
          routeBSPDPGeneratorRow M n hn2 htb hns
              ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
                (routeBRicherFiniteRowsCandidateGauge
                  M n hn2 htb hns rows)) p)
              S shift =
            Finset.univ.sum (fun j => coeff j • rows j)
          ∧
          routeBSPDPGeneratorRow M n hn2 htb hns
              ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
                (routeBRicherFiniteRowsCandidateGauge
                  M n hn2 htb hns rows)) p)
              S shift
            ∈
            mlBlockedSpdpSubspace
              (cook_levin_compilation M n hn2 htb hns).partition
              spdpKappa ell p)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
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
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_deltaEqRateKappa
      (N := N) (d := d)
      M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
      rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_projectedGenerator_linearCombination
        M n hn2 htb hns rows hgen)
      cover Q i hrow hextract hsource

/-- Same finite-row concrete assembly with the P-window cover reduced to the
current concreteW H3/H4/I5 closure frontier. -/
theorem routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_linearCombination_concreteWClosure_deltaEqRateKappa
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
    (hgen :
      forall (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        ∃ coeff : Fin m -> Rat,
          routeBSPDPGeneratorRow M n hn2 htb hns
              ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
                (routeBRicherFiniteRowsCandidateGauge
                  M n hn2 htb hns rows)) p)
              S shift =
            Finset.univ.sum (fun j => coeff j • rows j)
          ∧
          routeBSPDPGeneratorRow M n hn2 htb hns
              ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
                (routeBRicherFiniteRowsCandidateGauge
                  M n hn2 htb hns rows)) p)
              S shift
            ∈
            mlBlockedSpdpSubspace
              (cook_levin_compilation M n hn2 htb hns).partition
              spdpKappa ell p)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn2 htb hns hn4)
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
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_linearCombination_deltaEqRateKappa
      (N := N) (d := d)
      M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
      rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      hgen
      (routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_closureFrontier
        M n hn2 htb hns hn4 hFrontier)
      Q i hrow hextract hsource

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_linearCombination_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_linearCombination_concreteWClosure_deltaEqRateKappa

end PallLean.Paper93.Paper283

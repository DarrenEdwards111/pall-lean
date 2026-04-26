import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteReducedCertificate
import PallLean.Paper93.Paper283.RouteBRicherGaugeRankBudget
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteNP
import PallLean.Paper93.Paper283.RouteBBridgeAConcreteBudget
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos

/-!
# Concrete assembly for the richer finite-row Route B gauge

This file is the narrow integration surface for the current Route B
finite-row path.  It fixes the finite row family to the closed one-row
Cook-Levin NP witness, fixes the matrix to the concrete compiled gadget, and
uses the full spectral window.

The remaining assumptions are exactly the not-yet-closed Pi-star-side data:
the scalar Bridge A budget, the SPDP containment certificate for the one-row
candidate, and the unprojected P-window finite-span cover.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- Remaining concrete Route B assembly inputs after the closed row-count,
NP-witness, and compiled-gadget spectral/rank facts are used.

The finite-row candidate is fixed to `routeBRicherConcreteNPWitnessRows`, and
the matrix is fixed to `compiledGadget eta N`.  The budget is stated in the
compiled pocket-family form proved equivalent to the active rank sum by
`RouteBBridgeAConcreteSpectralFloor`. -/
structure RouteBRicherGaugeConcreteAssemblyCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) where
  N : Nat
  d : Nat
  alpha : Real
  beta : Real
  alpha0 : Real
  kappa : Nat
  gadgetN : Nat
  G : PallLean.Paper93.Concrete.RegularGraphFixed N d
  chi : TseitinCharge N
  Phi : Fin N -> Real
  eta : Real
  theta : Real
  delta : Real
  rankLogRate : Real
  N_pos : 1 <= N
  eta_pos : 0 < eta
  theta_pos : 0 < theta
  alpha_pos : 0 < alpha
  alpha0_pos : 0 < alpha0
  gadgetN_ge_two : 2 <= gadgetN
  rankLogRate_nonneg : 0 <= rankLogRate
  delta_le_rankLogRate_kappa : delta <= rankLogRate * (kappa : Real)
  spectral_floor_budget :
    rankLogRate *
        (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
          (PallLean.Paper93.DeepMath.BridgeB.pocketFamily
            alpha kappa gadgetN).rank : Nat) : Real) <=
      (N : Real) * Real.log (1 + theta * eta)
  spdp_containment :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- The positive compiled gadget has enough matrix rank for the one concrete
finite row. -/
theorem one_le_compiledGadget_rank_of_positive_coupling
    {N : Nat} {eta : Real} (heta : 0 < eta) (hN : 1 <= N) :
    1 <= (compiledGadget eta N).rank := by
  rw [compiledGadget_rank_full eta N heta hN]
  exact hN

/-- Assemble the previous concrete reduced certificate from the narrow
remaining assembly inputs. -/
noncomputable def routeBRicherGaugeConcreteReducedCertificate_of_concreteAssembly
    {M : DTM} {n : Nat} (hn : n >= 2 ^ 804) {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert :
      RouteBRicherGaugeConcreteAssemblyCertificate M n hn2 htb hns) :
    RouteBRicherGaugeConcreteReducedCertificate M n hn2 htb hns where
  N := cert.N
  d := cert.d
  alpha := cert.alpha
  beta := cert.beta
  alpha0 := cert.alpha0
  kappa := cert.kappa
  gadgetN := cert.gadgetN
  G := cert.G
  chi := cert.chi
  Phi := cert.Phi
  theta := cert.theta
  delta := cert.delta
  rankLogRate := cert.rankLogRate
  lambdaFloor := cert.eta
  A := compiledGadget cert.eta cert.N
  hA := compiledGadget_posSemidef_of_positive_coupling
    (N := cert.N) cert.eta cert.eta_pos
  spectralWindow := Finset.univ
  rowCount := 1
  rows := routeBRicherConcreteNPWitnessRows M n hn2 htb hns
  theta_pos := cert.theta_pos
  alpha_pos := cert.alpha_pos
  alpha0_pos := cert.alpha0_pos
  gadgetN_ge_two := cert.gadgetN_ge_two
  rankLogRate_nonneg := cert.rankLogRate_nonneg
  delta_le_rankLogRate_kappa := cert.delta_le_rankLogRate_kappa
  lambdaFloor_nonneg := cert.eta_pos.le
  eigenvalue_floor := by
    intro i _hi
    exact compiledGadget_eigenvalue_floor cert.eta cert.eta_pos
      (compiledGadget_posSemidef_of_positive_coupling
        (N := cert.N) cert.eta cert.eta_pos) i
  spectral_floor_budget := by
    simpa [cookLevinPocketLocalGadgetFamily, cookLevinPocketLocalGadget,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_mul] using
      cert.spectral_floor_budget
  rowSpan_rank_le_matrix_rank := by
    have hrow :
        (1 : Nat) <= (compiledGadget cert.eta cert.N).rank :=
      one_le_compiledGadget_rank_of_positive_coupling
        cert.eta_pos cert.N_pos
    exact_mod_cast
      le_trans
        (finiteRowsSubmodule_finrank_le_card
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns))
        hrow
  spdp_containment := cert.spdp_containment
  p_window_cover := cert.p_window_cover
  Q := routeBRicherConcreteNPWitnessQ M n hn2 htb hns
  witness_row := 0
  witness_row_eq_embed :=
    routeBRicherConcreteNPWitnessRows_eq_embed M n hn2 htb hns 0
  extracts_compiled :=
    routeBRicherConcreteNPWitnessRows_extracts_compiled M n hn2 htb hns
  source_lower_bound :=
    routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
      M n hn hn2 htb hns

/-- Reduced Route B certificate from the concrete richer-gauge assembly. -/
theorem routeBReducedCertificate_of_richerGaugeConcreteAssembly
    {M : DTM} {n : Nat} (hn : n >= 2 ^ 804) {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert :
      RouteBRicherGaugeConcreteAssemblyCertificate M n hn2 htb hns) :
    RouteBReducedCertificate M n hn2 htb hns :=
  routeBReducedCertificate_of_richerGaugeConcreteReducedCertificate
    (routeBRicherGaugeConcreteReducedCertificate_of_concreteAssembly
      hn cert)

/-- Final per-instance Route B certificate from the concrete richer-gauge
assembly. -/
theorem routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly
    {M : DTM} {n : Nat} (hn : n >= 2 ^ 804) {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert :
      RouteBRicherGaugeConcreteAssemblyCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_richerGaugeConcreteReducedCertificate
    (routeBRicherGaugeConcreteReducedCertificate_of_concreteAssembly
      hn cert)

/-- Concrete assembly with the Bridge A scalar budget filled by the explicit
rate schedule
`rankLogRate = log (1 + theta * eta) / (pocketFamily alpha kappa gadgetN).rank`.

After this specialization, the remaining Route B content is exactly the two
finite-row gauge obligations: SPDP containment and the P-window finite-span
cover. -/
theorem routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_logDivBudget
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
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  have hlog_nonneg : 0 <= Real.log (1 + theta * eta) :=
    log_one_add_theta_mul_eta_nonneg htheta heta
  have hrank_pos_nat : 0 < (pocketFamily alpha kappa gadgetN).rank :=
    pocketFamily_rank_pos_of_kappa_pos alpha kappa gadgetN
      halpha hkappa hgadgetN
  have hrank_pos_real :
      0 < ((pocketFamily alpha kappa gadgetN).rank : Real) := by
    exact_mod_cast hrank_pos_nat
  exact
    routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly
      hn
      ({ N := N
         d := d
         alpha := alpha
         beta := beta
         alpha0 := alpha0
         kappa := kappa
         gadgetN := gadgetN
         G := G
         chi := chi
         Phi := Phi
         eta := eta
         theta := theta
         delta := delta
         rankLogRate :=
          Real.log (1 + theta * eta) /
            ((pocketFamily alpha kappa gadgetN).rank : Real)
         N_pos := hN
         eta_pos := heta
         theta_pos := htheta
         alpha_pos := halpha
         alpha0_pos := halpha0
         gadgetN_ge_two := hgadgetN
         rankLogRate_nonneg := div_nonneg hlog_nonneg hrank_pos_real.le
         delta_le_rankLogRate_kappa := hdelta_rate
         spectral_floor_budget :=
          concreteBridgeA_spectral_budget_log_div_pocketRank
            alpha beta alpha0 kappa gadgetN G chi Phi
            halpha hkappa hgadgetN heta htheta
         spdp_containment := hcontain
         p_window_cover := cover } :
        RouteBRicherGaugeConcreteAssemblyCertificate M n hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms one_le_compiledGadget_rank_of_positive_coupling
#print axioms routeBRicherGaugeConcreteReducedCertificate_of_concreteAssembly
#print axioms routeBReducedCertificate_of_richerGaugeConcreteAssembly
#print axioms routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly
#print axioms routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_logDivBudget

end PallLean.Paper93.Paper283

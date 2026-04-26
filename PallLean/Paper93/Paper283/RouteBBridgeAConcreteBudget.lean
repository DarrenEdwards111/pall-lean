import PallLean.Paper93.Paper283.RouteBBridgeAConcreteSpectralFloor

/-!
# Route B Bridge A concrete spectral budget

This file isolates the remaining arithmetic after
`RouteBBridgeAConcreteSpectralFloor`: the full-span spectral floor reduces the
Bridge A lower-logdet package to

`rankLogRate * (|activeSet| * pocketRank) <= N * log (1 + theta * eta)`.

The lemmas below discharge this from the elementary facts that the active set
has at most `N` vertices and that the per-pocket rank-rate is bounded by the
single-slot spectral floor.  A concrete rate schedule

`rankLogRate = log (1 + theta * eta) / pocketRank`

is also packaged for the checked Cook-Levin pocket family when `kappa > 0`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The Bridge A active set has at most the ambient number of vertices, as a
real-valued inequality in the exact form used by the spectral-budget
arithmetic. -/
theorem activeSet_card_cast_le_ambient {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) :
    ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card : Real) <=
      (N : Real) := by
  have hcard :
      (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card <= N :=
    activeSet_card_le alpha beta alpha0 G chi Phi
  exact_mod_cast hcard

/-- Positivity of `theta` and `eta` gives the nonnegative log floor needed to
scale the active-set cardinality bound. -/
theorem log_one_add_theta_mul_eta_nonneg {theta eta : Real}
    (htheta : 0 < theta) (heta : 0 < eta) :
    0 <= Real.log (1 + theta * eta) := by
  have hprod : 0 <= theta * eta := mul_nonneg htheta.le heta.le
  have hone : (1 : Real) <= 1 + theta * eta := by linarith
  exact Real.log_nonneg hone

/-- The concrete Bridge A budget follows from the active-set cardinality bound
and a per-pocket-rank rate inequality. -/
theorem concreteBridgeA_spectral_budget_of_rankLogRate_mul_pocketRank_le_log
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta rankLogRate : Real}
    (hlog_nonneg : 0 <= Real.log (1 + theta * eta))
    (hrate_rank :
      rankLogRate *
          ((pocketFamily alpha kappa gadgetN).rank : Real) <=
        Real.log (1 + theta * eta)) :
    rankLogRate *
        (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
          (pocketFamily alpha kappa gadgetN).rank : Nat) : Real) <=
      (N : Real) * Real.log (1 + theta * eta) := by
  let S := activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi
  let R := (pocketFamily alpha kappa gadgetN).rank
  let L := Real.log (1 + theta * eta)
  have hcard : (S.card : Real) <= (N : Real) := by
    simpa [S] using activeSet_card_cast_le_ambient alpha beta alpha0 G chi Phi
  have hleft :
      (S.card : Real) * (rankLogRate * (R : Real)) <=
        (S.card : Real) * L :=
    mul_le_mul_of_nonneg_left (by simpa [R, L] using hrate_rank)
      (Nat.cast_nonneg S.card)
  have hright : (S.card : Real) * L <= (N : Real) * L :=
    mul_le_mul_of_nonneg_right hcard (by simpa [L] using hlog_nonneg)
  calc
    rankLogRate * (((S.card * R : Nat) : Real))
        = (S.card : Real) * (rankLogRate * (R : Real)) := by
          rw [Nat.cast_mul]
          ring
    _ <= (S.card : Real) * L := hleft
    _ <= (N : Real) * L := hright

/-- If the concrete pocket rank has been separately identified with `kappa`,
the remaining budget is just the scalar inequality
`rankLogRate * kappa <= log (1 + theta * eta)`. -/
theorem concreteBridgeA_spectral_budget_of_pocketRank_eq_kappa
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta rankLogRate : Real}
    (hlog_nonneg : 0 <= Real.log (1 + theta * eta))
    (hpocketRank :
      (pocketFamily alpha kappa gadgetN).rank = kappa)
    (hrate_kappa :
      rankLogRate * (kappa : Real) <= Real.log (1 + theta * eta)) :
    rankLogRate *
        (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
          (pocketFamily alpha kappa gadgetN).rank : Nat) : Real) <=
      (N : Real) * Real.log (1 + theta * eta) := by
  exact
    concreteBridgeA_spectral_budget_of_rankLogRate_mul_pocketRank_le_log
      alpha beta alpha0 kappa gadgetN G chi Phi hlog_nonneg
      (by simpa [hpocketRank] using hrate_kappa)

/-- Positive `kappa` makes the checked Cook-Levin pocket family have positive
rank. -/
theorem pocketFamily_rank_pos_of_kappa_pos
    (alpha : Real) (kappa gadgetN : Nat)
    (halpha : 0 < alpha) (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN) :
    0 < (pocketFamily alpha kappa gadgetN).rank := by
  exact lt_of_lt_of_le hkappa
    (PallLean.Paper93.DeepMath.CookLevin.bridge_B_kappa_pocket
      alpha kappa gadgetN halpha hgadgetN)

/-- Concrete spectral-budget schedule: choose the rank-log rate to be the
single-slot spectral floor divided by the checked pocket rank. -/
theorem concreteBridgeA_spectral_budget_log_div_pocketRank
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (halpha : 0 < alpha) (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (heta : 0 < eta) (htheta : 0 < theta) :
    (Real.log (1 + theta * eta) /
          ((pocketFamily alpha kappa gadgetN).rank : Real)) *
        (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
          (pocketFamily alpha kappa gadgetN).rank : Nat) : Real) <=
      (N : Real) * Real.log (1 + theta * eta) := by
  have hlog_nonneg : 0 <= Real.log (1 + theta * eta) :=
    log_one_add_theta_mul_eta_nonneg htheta heta
  have hrank_pos_nat : 0 < (pocketFamily alpha kappa gadgetN).rank :=
    pocketFamily_rank_pos_of_kappa_pos alpha kappa gadgetN
      halpha hkappa hgadgetN
  have hrank_pos_real :
      0 < ((pocketFamily alpha kappa gadgetN).rank : Real) := by
    exact_mod_cast hrank_pos_nat
  have hrate_rank :
      (Real.log (1 + theta * eta) /
          ((pocketFamily alpha kappa gadgetN).rank : Real)) *
          ((pocketFamily alpha kappa gadgetN).rank : Real) <=
        Real.log (1 + theta * eta) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hrank_pos_real)]
  exact
    concreteBridgeA_spectral_budget_of_rankLogRate_mul_pocketRank_le_log
      alpha beta alpha0 kappa gadgetN G chi Phi hlog_nonneg hrate_rank

/-- Full Bridge A lower-logdet package for the concrete compiled gadget under
the explicit rate schedule
`log (1 + theta * eta) / (pocketFamily alpha kappa gadgetN).rank`.

The only remaining semantic side condition is the requested lower local floor:
`delta <= rankLogRate * kappa`. -/
theorem bridgeA_rankLogDetLowerHypotheses_of_cookLevinPocket_compiledGadget_log_div_pocketRank
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta delta : Real}
    (halpha : 0 < alpha) (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (heta : 0 < eta) (htheta : 0 < theta)
    (hdelta_rate :
      delta <=
        (Real.log (1 + theta * eta) /
            ((pocketFamily alpha kappa gadgetN).rank : Real)) *
          (kappa : Real)) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi
      (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
      (Real.log (1 + theta * eta) /
        ((pocketFamily alpha kappa gadgetN).rank : Real))
      (Real.log
        (((1 : Matrix (Fin N) (Fin N) Real) +
          theta • (compiledGadget eta N)).det))
      delta := by
  have hlog_nonneg : 0 <= Real.log (1 + theta * eta) :=
    log_one_add_theta_mul_eta_nonneg htheta heta
  have hrank_pos_nat : 0 < (pocketFamily alpha kappa gadgetN).rank :=
    pocketFamily_rank_pos_of_kappa_pos alpha kappa gadgetN
      halpha hkappa hgadgetN
  have hrank_pos_real :
      0 < ((pocketFamily alpha kappa gadgetN).rank : Real) := by
    exact_mod_cast hrank_pos_nat
  have hrate_nonneg :
      0 <=
        Real.log (1 + theta * eta) /
          ((pocketFamily alpha kappa gadgetN).rank : Real) :=
    div_nonneg hlog_nonneg hrank_pos_real.le
  exact
    bridgeA_rankLogDetLowerHypotheses_of_cookLevinPocket_compiledGadget_spectral_floor
      alpha beta alpha0 kappa gadgetN G chi Phi
      heta htheta hrate_nonneg hdelta_rate
      (concreteBridgeA_spectral_budget_log_div_pocketRank
        alpha beta alpha0 kappa gadgetN G chi Phi
        halpha hkappa hgadgetN heta htheta)

/-! ## Axiom audit anchors -/

#print axioms activeSet_card_cast_le_ambient
#print axioms log_one_add_theta_mul_eta_nonneg
#print axioms concreteBridgeA_spectral_budget_of_rankLogRate_mul_pocketRank_le_log
#print axioms concreteBridgeA_spectral_budget_of_pocketRank_eq_kappa
#print axioms pocketFamily_rank_pos_of_kappa_pos
#print axioms concreteBridgeA_spectral_budget_log_div_pocketRank
#print axioms bridgeA_rankLogDetLowerHypotheses_of_cookLevinPocket_compiledGadget_log_div_pocketRank

end PallLean.Paper93.Paper283

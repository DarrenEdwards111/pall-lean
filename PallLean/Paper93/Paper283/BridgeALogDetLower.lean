import Mathlib.Tactic
import PallLean.Paper93.Paper283.RouteBRound1Bridge

/-!
# Bridge A lower log-det interface

`RouteBRound1Bridge` consumes the scalar lower estimate

`delta * |S| <= logDet`

over the Bridge A active set `S`.  The real paper-level analytic step is the
local barrier/log-det lower bound.  This file does not pretend to prove that
analytic estimate.  Instead it exposes two checked interfaces around it:

* `BridgeAActiveLogDetLowerHypotheses`: per-active-vertex local log-det
  contributions sum into the global `logDet`;
* `BridgeARankLogDetLowerHypotheses`: the remaining lower-barrier estimate is
  stated against the checked Bridge A total local-rank budget.

The main algebraic theorem is
`bridgeA_logDet_lower_from_rank_budget`: Bridge A's active rank budget plus the
rank-to-logdet lower-barrier hypothesis imply exactly the `delta * |S| <=
logDet` input needed downstream.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- Honest local-contribution form of the missing lower log-det estimate.

The first field says every active vertex contributes at least `delta` to the
local lower-barrier account.  The second field is the analytic aggregation
statement saying those local contributions are dominated by the global
`logDet`. -/
structure BridgeAActiveLogDetLowerHypotheses {N d : Nat}
    (alpha beta alpha0 delta logDet : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (localLogDet : Fin N -> Real) : Prop where
  active_local_logDet_lower :
    ∀ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
      delta <= localLogDet v
  active_logDet_sum_le_global :
    (∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
      localLogDet v) <= logDet

/-- Per-active-vertex lower-barrier contributions imply the scalar lower
log-det estimate consumed by Route B. -/
theorem bridgeA_logDet_lower_from_active_contributions {N d : Nat}
    (alpha beta alpha0 delta logDet : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (localLogDet : Fin N -> Real)
    (hlower :
      BridgeAActiveLogDetLowerHypotheses
        alpha beta alpha0 delta logDet G chi Phi localLogDet) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet := by
  classical
  have hsum :
      (∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        delta) <=
      (∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        localLogDet v) := by
    exact Finset.sum_le_sum hlower.active_local_logDet_lower
  have hconst :
      (∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        delta) =
      ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
        Real) * delta := by
    simp
  calc
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real)
        = ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) * delta := by ring
    _ =
        ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          delta := hconst.symm
    _ <=
        ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          localLogDet v := hsum
    _ <= logDet := hlower.active_logDet_sum_le_global

/-- Rank-budget form of the remaining lower-barrier estimate.

`rankLogRate` is the real amount of log-det lower barrier credited per unit of
local gadget rank.  The third field is the genuine analytic content still not
proved here: the global `logDet` dominates this rate times the active local
rank sum.  The first two fields are algebraic side conditions needed to turn
the checked Bridge A budget `|S| * kappa <= totalRank` into the scalar
`delta * |S|` lower bound. -/
structure BridgeARankLogDetLowerHypotheses {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (rankLogRate logDet delta : Real) : Prop where
  rankLogRate_nonneg : 0 <= rankLogRate
  delta_le_rankLogRate_kappa : delta <= rankLogRate * (kappa : Real)
  rankLogRate_totalRank_le_logDet :
    rankLogRate *
        ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (gadgetFamily v).rank) : Real) <= logDet

/-- Bridge A rank budget plus a named rank-to-logdet lower-barrier hypothesis
produce exactly the lower `logDet` input required by `RouteBRound1Bridge`. -/
theorem bridgeA_logDet_lower_from_rank_budget {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (halpha0 : 0 < alpha0)
    (hGadgetRank :
      ∀ v : Fin N,
        alpha0 <= localEnergy alpha beta G chi Phi v ->
          kappa <= (gadgetFamily v).rank)
    {rankLogRate logDet delta : Real}
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi gadgetFamily
        rankLogRate logDet delta) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet := by
  classical
  have hbudget_nat :
      (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
          kappa <=
        ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (gadgetFamily v).rank :=
    bridgeA_activeSet_rank_budget
      alpha beta alpha0 kappa G chi Phi gadgetFamily halpha0 hGadgetRank
  have hbudget_real :
      (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
          kappa : Nat) : Real) <=
        ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (gadgetFamily v).rank) : Real) := by
    exact_mod_cast hbudget_nat
  have hcard_nonneg :
      0 <=
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) :=
    Nat.cast_nonneg _
  have hdelta_card :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <=
        (rankLogRate * (kappa : Real)) *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) :=
    mul_le_mul_of_nonneg_right
      hlower.delta_le_rankLogRate_kappa hcard_nonneg
  have hrate_budget :
      rankLogRate *
          (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
            kappa : Nat) : Real) <=
        rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real) :=
    mul_le_mul_of_nonneg_left hbudget_real hlower.rankLogRate_nonneg
  calc
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real)
        <=
          (rankLogRate * (kappa : Real)) *
            ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
              Real) := hdelta_card
    _ =
        rankLogRate *
          (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
            kappa : Nat) : Real) := by
      rw [Nat.cast_mul]
      ring
    _ <=
        rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real) := hrate_budget
    _ <= logDet := hlower.rankLogRate_totalRank_le_logDet

/-- Cook-Levin `kappa`-pocket version of the lower log-det estimate.  This is
the shape intended for the round-1 Route B spectral core. -/
theorem bridgeA_cookLevin_logDet_lower_from_rank_budget {N d : Nat}
    (alpha beta alpha0 : Real) (kappa n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hn : 2 <= n)
    {rankLogRate logDet delta : Real}
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa n)
        rankLogRate logDet delta) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet := by
  exact bridgeA_logDet_lower_from_rank_budget
    alpha beta alpha0 kappa G chi Phi
    (cookLevinPocketLocalGadgetFamily N alpha kappa n)
    halpha0
    (cookLevin_hGadgetRank_kappa
      alpha beta alpha0 kappa n G chi Phi halpha hn)
    hlower

/-- Route B round-1 core with the lower log-det input discharged from the
Cook-Levin active-rank budget and a named rank-to-logdet lower-barrier
hypothesis. -/
theorem routeB_round1_cookLevin_spectral_core_from_rank_logdet_lower
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hn : 2 <= n)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa n)
        rankLogRate logDet delta) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
        kappa <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        ((cookLevinPocketLocalGadgetFamily N alpha kappa n) v).rank
    ∧
    (delta / bridgeBLogCapacity theta normBound) *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <=
      (rankA : Real) := by
  exact routeB_round1_cookLevin_spectral_core
    alpha beta alpha0 kappa n G chi Phi halpha halpha0 hn
    htheta hnorm hspec
    (bridgeA_cookLevin_logDet_lower_from_rank_budget
      alpha beta alpha0 kappa n G chi Phi halpha halpha0 hn hlower)

/-- Variant of the round-1 core where the lower log-det input is supplied by
per-active-vertex local contributions. -/
theorem routeB_round1_cookLevin_spectral_core_from_active_logdet_lower
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hn : 2 <= n)
    {theta normBound logDet delta : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (localLogDet : Fin N -> Real)
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeAActiveLogDetLowerHypotheses
        alpha beta alpha0 delta logDet G chi Phi localLogDet) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
        kappa <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        ((cookLevinPocketLocalGadgetFamily N alpha kappa n) v).rank
    ∧
    (delta / bridgeBLogCapacity theta normBound) *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <=
      (rankA : Real) := by
  exact routeB_round1_cookLevin_spectral_core
    alpha beta alpha0 kappa n G chi Phi halpha halpha0 hn
    htheta hnorm hspec
    (bridgeA_logDet_lower_from_active_contributions
      alpha beta alpha0 delta logDet G chi Phi localLogDet hlower)

/-! ## Axiom audit anchors -/

#print axioms bridgeA_logDet_lower_from_active_contributions
#print axioms bridgeA_logDet_lower_from_rank_budget
#print axioms bridgeA_cookLevin_logDet_lower_from_rank_budget
#print axioms routeB_round1_cookLevin_spectral_core_from_rank_logdet_lower
#print axioms routeB_round1_cookLevin_spectral_core_from_active_logdet_lower

end PallLean.Paper93.Paper283

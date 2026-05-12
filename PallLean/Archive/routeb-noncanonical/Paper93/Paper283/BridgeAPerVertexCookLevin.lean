import PallLean.Paper93.Paper283.BridgeALogDetLower
import PallLean.Paper93.DeepMath.CookLevin.BridgeB

/-!
# Per-vertex Bridge A Cook-Levin pocket gadgets

Paper §28.3 Bridge A is a local analytic-to-algebraic implication:

`E_v >= alpha0 > 0 -> rk_SPDP(Q_v) >= kappa`.

The older `cookLevinPocketLocalGadgetFamily` gives the right rank inequality
uniformly from a positive global coupling, but it does not use the local
energy hypothesis.  This file records the paper-faithful per-vertex shape:
the local compiled pocket at `v` is coupled by the local energy `E_v`, so the
Bridge A threshold supplies exactly the positivity needed by the checked
Cook-Levin pocket-rank theorem.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- Per-vertex Cook-Levin pocket gadget whose coupling is the local Bridge A
energy `E_v`.  This is the local-gadget wrapper for the paper-faithful Bridge A
direction: the polynomial/matrix gadget is supplied by the compiler, while the
variational energy controls its positive coupling. -/
noncomputable def energyCoupledCookLevinPocketLocalGadget {N d : Nat}
    (alpha beta : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) :
    LocalGadget N v where
  rank :=
    (PallLean.Paper93.DeepMath.BridgeB.pocketFamily
      (localEnergy alpha beta G chi Phi v) kappa gadgetN).rank

/-- The per-vertex energy-coupled Cook-Levin pocket gadget family. -/
noncomputable def energyCoupledCookLevinPocketLocalGadgetFamily {N d : Nat}
    (alpha beta : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) :
    forall v : Fin N, LocalGadget N v :=
  fun v =>
    energyCoupledCookLevinPocketLocalGadget
      alpha beta kappa gadgetN G chi Phi v

/-- Paper-faithful per-vertex Bridge A for the energy-coupled Cook-Levin
pocket gadget: a positive local-energy threshold gives the positivity
hypothesis needed by the checked `kappa`-pocket rank theorem. -/
theorem energyCoupledCookLevinPocketLocalGadget_rank_kappa {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha0 : 0 < alpha0) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <=
      ((energyCoupledCookLevinPocketLocalGadgetFamily
        alpha beta kappa gadgetN G chi Phi) v).rank := by
  have hlocal :
      0 < localEnergy alpha beta G chi Phi v :=
    lt_of_lt_of_le halpha0 hE
  simpa [energyCoupledCookLevinPocketLocalGadgetFamily,
    energyCoupledCookLevinPocketLocalGadget] using
    PallLean.Paper93.DeepMath.CookLevin.bridge_B_kappa_pocket
      (localEnergy alpha beta G chi Phi v) kappa gadgetN hlocal hgadgetN

/-- The exact `hGadgetRank` hypothesis required by
`bridgeA_activeSet_rank_budget`, discharged from the local energy threshold
instead of from a uniform positive coupling. -/
theorem energyCoupledCookLevin_hGadgetRank_kappa {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0) (hgadgetN : 2 <= gadgetN) :
    forall v : Fin N,
      alpha0 <= localEnergy alpha beta G chi Phi v ->
        kappa <=
          ((energyCoupledCookLevinPocketLocalGadgetFamily
            alpha beta kappa gadgetN G chi Phi) v).rank := by
  intro v hE
  exact
    energyCoupledCookLevinPocketLocalGadget_rank_kappa
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha0 hgadgetN hE

/-- Active-set Bridge A rank budget for the energy-coupled Cook-Levin pocket
family.  This is the aggregate version of the paper §28.3 per-vertex theorem
over `S = {v | alpha0 <= E_v}`. -/
theorem bridgeA_activeSet_rank_budget_energyCoupledCookLevin_kappa {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0) (hgadgetN : 2 <= gadgetN) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card * kappa <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        ((energyCoupledCookLevinPocketLocalGadgetFamily
          alpha beta kappa gadgetN G chi Phi) v).rank := by
  exact
    bridgeA_activeSet_rank_budget
      alpha beta alpha0 kappa G chi Phi
      (energyCoupledCookLevinPocketLocalGadgetFamily
        alpha beta kappa gadgetN G chi Phi)
      halpha0
      (energyCoupledCookLevin_hGadgetRank_kappa
        alpha beta alpha0 kappa gadgetN G chi Phi halpha0 hgadgetN)

/-- Lower-logdet Bridge A input for the energy-coupled Cook-Levin pocket
family.  The remaining analytic lower-barrier estimate is still the explicit
`BridgeARankLogDetLowerHypotheses` field; the per-vertex energy-to-rank side
is now discharged by the theorem above. -/
theorem bridgeA_energyCoupledCookLevin_logDet_lower_from_rank_budget
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0) (hgadgetN : 2 <= gadgetN)
    {rankLogRate logDet delta : Real}
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (energyCoupledCookLevinPocketLocalGadgetFamily
          alpha beta kappa gadgetN G chi Phi)
        rankLogRate logDet delta) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet := by
  exact
    bridgeA_logDet_lower_from_rank_budget
      alpha beta alpha0 kappa G chi Phi
      (energyCoupledCookLevinPocketLocalGadgetFamily
        alpha beta kappa gadgetN G chi Phi)
      halpha0
      (energyCoupledCookLevin_hGadgetRank_kappa
        alpha beta alpha0 kappa gadgetN G chi Phi halpha0 hgadgetN)
      hlower

/-! ## Axiom audit anchors -/

#print axioms energyCoupledCookLevinPocketLocalGadget_rank_kappa
#print axioms energyCoupledCookLevin_hGadgetRank_kappa
#print axioms bridgeA_activeSet_rank_budget_energyCoupledCookLevin_kappa
#print axioms bridgeA_energyCoupledCookLevin_logDet_lower_from_rank_budget

end PallLean.Paper93.Paper283

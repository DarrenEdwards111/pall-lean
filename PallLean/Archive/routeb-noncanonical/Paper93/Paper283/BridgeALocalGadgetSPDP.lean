import PallLean.Paper93.Paper283.BridgeAConcreteGadget
import PallLean.Paper93.DeepMath.CookLevin.RankToSPDPBound

/-!
# Bridge A local SPDP-rank surface

This file exposes the per-vertex Bridge A conclusion in the language used by
the current Paper283 local-gadget interface:

`alpha0 <= E_v(Phi) -> kappa <= rk_SPDP(Q_v)`.

The existing `LocalGadget.rank` field is the local SPDP rank carried by the
compiler-side gadget wrapper.  The concrete specialization below uses the
checked Cook-Levin `kappa`-pocket family, so the local-energy hypothesis is
only the Bridge A trigger; the current uniform pocket compiler supplies the
rank lower bound independently of `v`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- The SPDP rank carried by a Paper283 local gadget. -/
def localGadgetSPDPRank {N : Nat} {v : Fin N}
    (Qv : LocalGadget N v) : Nat :=
  Qv.rank

/-- Pointwise Bridge A local SPDP-rank statement for a supplied local-gadget
family `Q_v`. -/
def BridgeALocalGadgetSPDPRankLowerBound {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v) : Prop :=
  forall v : Fin N,
    alpha0 <= localEnergy alpha beta G chi Phi v ->
      kappa <= localGadgetSPDPRank (gadgetFamily v)

/-- The explicit SPDP-rank statement is exactly the old `hGadgetRank` surface
after unfolding the rank accessor. -/
theorem bridgeA_hGadgetRank_of_localGadgetSPDPRankLowerBound {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (hspdp :
      BridgeALocalGadgetSPDPRankLowerBound
        alpha beta alpha0 kappa G chi Phi gadgetFamily) :
    forall v : Fin N,
      alpha0 <= localEnergy alpha beta G chi Phi v ->
        kappa <= (gadgetFamily v).rank := by
  intro v hv
  exact hspdp v hv

/-- Bridge A at a single vertex, stated directly as an SPDP-rank lower bound
for the local gadget `Q_v`. -/
theorem bridgeA_localGadget_spdpRank_lower_bound {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v)
    (halpha0 : 0 < alpha0)
    (hspdp :
      BridgeALocalGadgetSPDPRankLowerBound
        alpha beta alpha0 kappa G chi Phi gadgetFamily) :
    kappa <= localGadgetSPDPRank (gadgetFamily v) := by
  have hRank :
      forall v : Fin N,
        alpha0 <= localEnergy alpha beta G chi Phi v ->
          kappa <= (gadgetFamily v).rank :=
    bridgeA_hGadgetRank_of_localGadgetSPDPRankLowerBound
      alpha beta alpha0 kappa G chi Phi gadgetFamily hspdp
  simpa [localGadgetSPDPRank] using
    bridgeA_rank_lower_bound
      alpha beta alpha0 kappa G chi Phi v gadgetFamily hE halpha0 hRank

/-- Concrete per-vertex Bridge A SPDP-rank lower bound for the checked
Cook-Levin `kappa`-pocket local gadget family. -/
theorem cookLevinPocketLocalGadget_spdpRank_lower_bound {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <=
      localGadgetSPDPRank
        ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v) := by
  have _halpha0 : 0 < alpha0 := halpha0
  have _hE : alpha0 <= localEnergy alpha beta G chi Phi v := hE
  simpa [localGadgetSPDPRank, cookLevinPocketLocalGadgetFamily,
    cookLevinPocketLocalGadget] using
    PallLean.Paper93.DeepMath.CookLevin.SPDP_rank_lower_bound
      alpha kappa gadgetN halpha hgadgetN

/-- Family form of the concrete Cook-Levin pocket Bridge A SPDP-rank lower
bound.  This is the per-vertex local-gadget statement that can be fed back
into the existing active-set Bridge A budget route. -/
theorem cookLevinPocketLocalGadget_spdpRankLowerBound {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hgadgetN : 2 <= gadgetN) :
    BridgeALocalGadgetSPDPRankLowerBound
      alpha beta alpha0 kappa G chi Phi
      (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) := by
  intro v hE
  exact
    cookLevinPocketLocalGadget_spdpRank_lower_bound
      alpha beta alpha0 kappa gadgetN G chi Phi v
      halpha halpha0 hgadgetN hE

/-- Active-set Bridge A budget, restated with the explicit local SPDP-rank
accessor for the checked Cook-Levin pocket local gadgets. -/
theorem bridgeA_activeSet_spdpRank_budget_cookLevinPocket {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hgadgetN : 2 <= gadgetN) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card * kappa <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        localGadgetSPDPRank
          ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v) := by
  classical
  let S := activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi
  have hpoint :
      forall v, v ∈ S ->
        kappa <=
          localGadgetSPDPRank
            ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v) := by
    intro v hv
    exact
      cookLevinPocketLocalGadget_spdpRank_lower_bound
        alpha beta alpha0 kappa gadgetN G chi Phi v
        halpha halpha0 hgadgetN
        (activeSet_mem_energy alpha beta alpha0 G chi Phi hv)
  change
    S.card * kappa <=
      ∑ v ∈ S,
        localGadgetSPDPRank
          ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v)
  calc
    S.card * kappa = ∑ _v ∈ S, kappa := by
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    _ <=
        ∑ v ∈ S,
          localGadgetSPDPRank
            ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v) :=
      Finset.sum_le_sum hpoint

/-! ## Axiom audit anchors -/

#print axioms localGadgetSPDPRank
#print axioms BridgeALocalGadgetSPDPRankLowerBound
#print axioms bridgeA_hGadgetRank_of_localGadgetSPDPRankLowerBound
#print axioms bridgeA_localGadget_spdpRank_lower_bound
#print axioms cookLevinPocketLocalGadget_spdpRank_lower_bound
#print axioms cookLevinPocketLocalGadget_spdpRankLowerBound
#print axioms bridgeA_activeSet_spdpRank_budget_cookLevinPocket

end PallLean.Paper93.Paper283

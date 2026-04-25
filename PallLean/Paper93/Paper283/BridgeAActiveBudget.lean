import PallLean.Paper93.Paper283.BridgeATotalRank

/-!
# Bridge A active-set rank budget

This module removes one layer of indirection from the paper §28.3 Bridge A
route.  Earlier files exposed:

* `activeSet`: vertices whose local energy clears the threshold `alpha0`;
* `bridgeA_rank_lower_bound`: the per-vertex energy-to-rank implication,
  assuming the paper's local gadget-rank bridge;
* `bridgeA_totalRank_composition`: summation of per-vertex rank bounds.

Here we compose those pieces directly.  The resulting theorem has the exact
shape used by the N-Frame route:

`|S| * kappa <= sum_{v in S} rank(Q_v)`.

No polynomial/profile-collapse content is used here.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- Membership in the Bridge A active set is exactly the local-energy
threshold needed by the pointwise Bridge A rank theorem. -/
theorem activeSet_mem_energy {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {v : Fin N}
    (hv : v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi) :
    alpha0 <= localEnergy alpha beta G chi Phi v := by
  classical
  simpa [activeSet] using hv

/-- Bridge A pointwise rank bounds on the whole active set, derived from the
local energy predicate rather than supplied as a separate hypothesis. -/
theorem bridgeA_activeSet_perVertex_rank {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (halpha0 : 0 < alpha0)
    (hGadgetRank :
      ∀ v : Fin N,
        alpha0 <= localEnergy alpha beta G chi Phi v ->
          kappa <= (gadgetFamily v).rank) :
    ∀ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
      kappa <= (gadgetFamily v).rank := by
  intro v hv
  exact bridgeA_rank_lower_bound
    alpha beta alpha0 kappa G chi Phi v gadgetFamily
    (activeSet_mem_energy alpha beta alpha0 G chi Phi hv)
    halpha0 hGadgetRank

/-- The load-bearing Bridge A budget over the active set:
if every vertex whose local energy clears `alpha0` satisfies the paper's
local energy-to-rank bridge, then the active set contributes at least
`|S| * kappa` total local rank. -/
theorem bridgeA_activeSet_rank_budget {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (halpha0 : 0 < alpha0)
    (hGadgetRank :
      ∀ v : Fin N,
        alpha0 <= localEnergy alpha beta G chi Phi v ->
          kappa <= (gadgetFamily v).rank) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card * kappa <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        (gadgetFamily v).rank := by
  have hsum :=
    bridgeA_totalRank_composition
      alpha beta alpha0 kappa G chi Phi gadgetFamily
      (bridgeA_activeSet_perVertex_rank
        alpha beta alpha0 kappa G chi Phi gadgetFamily halpha0 hGadgetRank)
  simpa [bridgeA_totalRank_equals_card_kappa
    alpha beta alpha0 kappa G chi Phi] using hsum

/-- If the active set is nonempty and `kappa > 0`, Bridge A produces a
strictly positive total local-rank budget. -/
theorem bridgeA_activeSet_rank_sum_pos {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (halpha0 : 0 < alpha0)
    (hGadgetRank :
      ∀ v : Fin N,
        alpha0 <= localEnergy alpha beta G chi Phi v ->
          kappa <= (gadgetFamily v).rank)
    (hS :
      (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).Nonempty)
    (hkappa : 0 < kappa) :
    0 <
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        (gadgetFamily v).rank := by
  have hcard_pos :
      0 < (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :=
    Finset.card_pos.mpr hS
  have hbudget_pos :
      0 <
        (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
          kappa :=
    Nat.mul_pos hcard_pos hkappa
  exact lt_of_lt_of_le hbudget_pos
    (bridgeA_activeSet_rank_budget
      alpha beta alpha0 kappa G chi Phi gadgetFamily halpha0 hGadgetRank)

/-! ## Axiom audit anchors -/

#print axioms activeSet_mem_energy
#print axioms bridgeA_activeSet_perVertex_rank
#print axioms bridgeA_activeSet_rank_budget
#print axioms bridgeA_activeSet_rank_sum_pos

end PallLean.Paper93.Paper283

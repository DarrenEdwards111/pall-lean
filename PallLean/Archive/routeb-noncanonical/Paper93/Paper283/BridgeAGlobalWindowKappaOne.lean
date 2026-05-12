import PallLean.Paper93.Paper283.BridgeAKappaOneRouteBIntegration
import PallLean.Paper93.Paper283.BridgeALogDetLower

/-!
# Bridge A global/window route at kappa = 1

This file is a packaging layer for the already-proved real Cook-Levin local
block theorem at `kappa = 1`.

The local theorem in `BridgeAKappaOneCookLevinLocalBlock` proves that every
compiler variable supplies a nonzero first-order derivative row for the real
local block product `cookLevinLocalBlockQ`.  The integration file
`BridgeAKappaOneRouteBIntegration` already turns those pointwise facts into a
Route B local-gadget family over the graph/window vertices.  Here we expose the
global active-set consequence in the shape usually consumed downstream:

`activeSet.card <= sum local ranks`.

The final theorem also connects this real local-block rank budget to the
existing rank-to-logdet lower hypothesis interface at `kappa = 1`.  No final
projection claim is introduced here.
-/

namespace PallLean.Paper93.Paper283

open PaperFaithfulSeparation
open scoped BigOperators

/-- The real Cook-Levin local-block family used by the global/window
`kappa = 1` Bridge A route.  This is only a short alias for the family built
from `cookLevinLocalBlockQBridgeAData_one_assign`. -/
noncomputable def cookLevinLocalBlockQ_globalWindowLocalGadgetFamily_one
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real) :
    forall v : Fin n, LocalGadget n v :=
  cookLevinLocalBlockQ_routeBLocalGadgetFamily_one_assign
    M n hn htb hns alpha beta alpha0 G chi Phi

/-- Global/window active-set rank budget for the real `kappa = 1`
Cook-Levin local block family, stated directly as
`|activeSet| <= sum_v rank(Q_v)`.

This is the named adapter requested here: the load-bearing proof is
`cookLevinLocalBlockQ_routeB_activeSet_rank_budget_one_assign`, with the
trivial multiplication by `1` removed. -/
theorem cookLevinLocalBlockQ_globalWindow_activeSet_card_le_rank_sum_one
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real)
    (halpha0 : 0 < alpha0) :
    (activeSet (N := n) (d := d) alpha beta alpha0 G chi Phi).card <=
      ∑ v ∈ activeSet (N := n) (d := d) alpha beta alpha0 G chi Phi,
        (cookLevinLocalBlockQ_globalWindowLocalGadgetFamily_one
          M n hn htb hns alpha beta alpha0 G chi Phi v).rank := by
  simpa [cookLevinLocalBlockQ_globalWindowLocalGadgetFamily_one, Nat.mul_one]
    using
      (cookLevinLocalBlockQ_routeB_activeSet_rank_budget_one_assign
        M n hn htb hns alpha beta alpha0 G chi Phi halpha0)

/-- Same global/window rank budget, but with the local ranks unfolded to the
actual first-order blocked SPDP ranks of `cookLevinLocalBlockQ` on the compiler
block assigned to each window vertex. -/
theorem cookLevinLocalBlockQ_globalWindow_activeSet_card_le_spdpRank_sum_one
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real)
    (halpha0 : 0 < alpha0) :
    (activeSet (N := n) (d := d) alpha beta alpha0 G chi Phi).card <=
      ∑ v ∈ activeSet (N := n) (d := d) alpha beta alpha0 G chi Phi,
        MultilinearSPDP.mlBlockedSpdpRank
          (cook_levin_compilation M n hn htb hns).partition
          1 1
          (cookLevinLocalBlockQ M n hn htb hns
            ((cook_levin_compilation M n hn htb hns).partition.assign v)) := by
  simpa [
      cookLevinLocalBlockQ_globalWindowLocalGadgetFamily_one,
      cookLevinLocalBlockQ_routeBLocalGadgetFamily_one_assign,
      cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_one_assign,
      BridgeAPolynomialLocalGadget.toLocalGadget,
      Nat.mul_one]
    using
      (cookLevinLocalBlockQ_routeB_activeSet_rank_budget_one_assign
        M n hn htb hns alpha beta alpha0 G chi Phi halpha0)

/-- Rank-to-logdet lower-barrier connection for the real `kappa = 1`
Cook-Levin local-block global/window family.

The analytic input remains explicit as
`BridgeARankLogDetLowerHypotheses`; this theorem only plugs the checked
real local-block active rank budget into that interface. -/
theorem cookLevinLocalBlockQ_globalWindow_logDet_lower_from_rank_budget_one
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real)
    (halpha0 : 0 < alpha0)
    {rankLogRate logDet delta : Real}
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 1 G chi Phi
        (cookLevinLocalBlockQ_globalWindowLocalGadgetFamily_one
          M n hn htb hns alpha beta alpha0 G chi Phi)
        rankLogRate logDet delta) :
    delta *
        ((activeSet (N := n) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet := by
  exact
    bridgeA_logDet_lower_from_rank_budget
      alpha beta alpha0 1 G chi Phi
      (cookLevinLocalBlockQ_globalWindowLocalGadgetFamily_one
        M n hn htb hns alpha beta alpha0 G chi Phi)
      halpha0
      (cookLevinLocalBlockQ_routeB_hGadgetRank_one_assign
        M n hn htb hns alpha beta alpha0 G chi Phi)
      hlower

end PallLean.Paper93.Paper283

import PallLean.Paper93.Paper283.BridgeAKappaOneCookLevinLocalBlock
import PallLean.Paper93.Paper283.BridgeAActiveBudget

/-!
# Bridge A kappa = 1 data as a Route B local-gadget family

`BridgeAKappaOneCookLevinLocalBlock` proves the paper-faithful
energy-to-SPDP-rank statement for the real Cook-Levin local block polynomial
at `kappa = 1`.  This file only aggregates that checked data into the existing
Route B local-gadget family interface used by the active-set budget.

No new compiler or rank assumptions are introduced here.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- The already-proved `kappa = 1` Cook-Levin local block data as a
polynomial-bearing Bridge A family over the same vertex set as the Route B
graph. -/
noncomputable def cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_one_assign
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real) :
    forall v : Fin n,
      BridgeAPolynomialLocalGadget
        alpha beta alpha0 1 G chi Phi v :=
  cookLevinLocalBlockQ_polynomialLocalGadgetFamily
    M n hn htb hns alpha beta alpha0 1 G chi Phi
    (cookLevinLocalBlockQBridgeAData_one_assign
      M n hn htb hns alpha beta alpha0 G chi Phi)

/-- Forget the polynomial-bearing `kappa = 1` Cook-Levin family to the
rank-only `LocalGadget` family consumed by the existing Route B active-set
budget. -/
noncomputable def cookLevinLocalBlockQ_routeBLocalGadgetFamily_one_assign
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real) :
    forall v : Fin n, LocalGadget n v :=
  fun v =>
    (cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_one_assign
      M n hn htb hns alpha beta alpha0 G chi Phi v).toLocalGadget

/-- Route B's local rank hypothesis, supplied by the checked `kappa = 1`
Cook-Levin local block Bridge A data. -/
theorem cookLevinLocalBlockQ_routeB_hGadgetRank_one_assign
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real) :
    forall v : Fin n,
      alpha0 <= localEnergy alpha beta G chi Phi v ->
        1 <=
          (cookLevinLocalBlockQ_routeBLocalGadgetFamily_one_assign
            M n hn htb hns alpha beta alpha0 G chi Phi v).rank := by
  exact
    BridgeAPolynomialLocalGadget.family_to_hGadgetRank
      (cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_one_assign
        M n hn htb hns alpha beta alpha0 G chi Phi)

/-- The existing Bridge A active-set rank budget specialized to the real
Cook-Levin local block family at `kappa = 1`. -/
theorem cookLevinLocalBlockQ_routeB_activeSet_rank_budget_one_assign
    {d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real)
    (halpha0 : 0 < alpha0) :
    (activeSet (N := n) (d := d) alpha beta alpha0 G chi Phi).card * 1 <=
      ∑ v ∈ activeSet (N := n) (d := d) alpha beta alpha0 G chi Phi,
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_one_assign
          M n hn htb hns alpha beta alpha0 G chi Phi v).rank := by
  exact
    bridgeA_activeSet_rank_budget
      alpha beta alpha0 1 G chi Phi
      (cookLevinLocalBlockQ_routeBLocalGadgetFamily_one_assign
        M n hn htb hns alpha beta alpha0 G chi Phi)
      halpha0
      (cookLevinLocalBlockQ_routeB_hGadgetRank_one_assign
        M n hn htb hns alpha beta alpha0 G chi Phi)

end PallLean.Paper93.Paper283

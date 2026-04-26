import PallLean.Paper93.Paper283.BridgeAKappaGeneralBoolRows
import PallLean.Paper93.Paper283.RouteBBridgeAIntegration

/-!
# General-kappa real local-block Bridge A integration

The final Route B assembly still consumes the rank-only
`RouteBCompilerLocalBridgeA` surface over `cookLevinPocketLocalGadgetFamily`.
The real compiler-local polynomial work produces
`CookLevinLocalBlockQBridgeAData` instead.

This file connects those layers without hiding the remaining mathematical
input: to feed the current final Route B certificate, one must still identify
the rank of the real local-block polynomial gadget with the pocket-family rank
used by the existing analytic/log-det package.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- A proved real local-block Bridge A package gives a polynomial-bearing
Route B local gadget family. -/
noncomputable def cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi) :
    forall v : Fin N,
      BridgeAPolynomialLocalGadget
        alpha beta alpha0 kappa G chi Phi v :=
  cookLevinLocalBlockQ_polynomialLocalGadgetFamily
    M n hn htb hns alpha beta alpha0 kappa G chi Phi data

/-- Forget a real local-block polynomial-bearing family to the existing
rank-only `LocalGadget` interface. -/
noncomputable def cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi) :
    forall v : Fin N, LocalGadget N v :=
  fun v =>
    (cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
      M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget

/-- Pointwise Route B local rank hypothesis from real local-block Bridge A
data, before comparing it to the pocket-family surface. -/
theorem cookLevinLocalBlockQ_routeB_hGadgetRank_of_data
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi) :
    forall v : Fin N,
      alpha0 <= localEnergy alpha beta G chi Phi v ->
        kappa <=
          (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
            M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).rank := by
  exact
    BridgeAPolynomialLocalGadget.family_to_hGadgetRank
      (cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
        M n hn htb hns alpha beta alpha0 kappa G chi Phi data)

/-- Active-set budget using the real local-block polynomial family directly. -/
theorem cookLevinLocalBlockQ_routeB_activeSet_rank_budget_of_data
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card * kappa <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
          M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).rank := by
  exact
    bridgeA_activeSet_rank_budget
      alpha beta alpha0 kappa G chi Phi
      (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
        M n hn htb hns alpha beta alpha0 kappa G chi Phi data)
      halpha0
      (cookLevinLocalBlockQ_routeB_hGadgetRank_of_data
        M n hn htb hns alpha beta alpha0 kappa G chi Phi data)

/-- Adapter from real local-block Bridge A data to the final Route B
`RouteBCompilerLocalBridgeA` surface.  The remaining explicit input is the
rank-realization equality between the real local-block gadget and the pocket
family used by the current analytic/log-det package. -/
theorem routeBCompilerLocalBridgeA_of_cookLevinLocalBlockQBridgeAData
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi)
    (hrealizesPocket :
      forall v : Fin N,
        ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
          M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank =
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
    RouteBCompilerLocalBridgeA alpha beta alpha0 kappa gadgetN G chi Phi := by
  intro v hE
  have hlocal :
      kappa <=
        ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
          M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank :=
    (cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
      M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget_rank_lower_bound hE
  simpa [hrealizesPocket v] using hlocal

/-! ## Axiom audit anchors -/

#print axioms cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
#print axioms cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
#print axioms cookLevinLocalBlockQ_routeB_hGadgetRank_of_data
#print axioms cookLevinLocalBlockQ_routeB_activeSet_rank_budget_of_data
#print axioms routeBCompilerLocalBridgeA_of_cookLevinLocalBlockQBridgeAData

end PallLean.Paper93.Paper283

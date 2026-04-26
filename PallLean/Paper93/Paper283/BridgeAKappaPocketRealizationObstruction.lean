import PallLean.Paper93.Paper283.BridgeAKappaGeneralRouteBIntegration
import PallLean.Paper93.Paper283.BridgeAKappaLocalSupportObstruction
import PallLean.Paper93.Paper283.BridgeACompilerLocalPolynomial

/-!
# Pocket-realization obstruction for bounded real local blocks

The current final Route B bridge can consume real Cook-Levin local-block
Bridge A data only after an explicit equality identifying the rank of that
real local-block polynomial gadget with the rank of the analytic
`cookLevinPocketLocalGadgetFamily` surface.

This file records the sharp obstruction to that equality.  If the real local
block product sees fewer than `kappa` variables, its strict-`kappa` blocked
SPDP rank is zero.  But the pocket surface has rank at least `kappa` whenever
the coupling is positive and the matrix gadget has size at least two.  Thus
the current pocket-realization equality cannot be the way to close paper-scale
`kappa` from one bounded local block.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-- The forgotten rank of the real local-block polynomial-bearing gadget is
exactly the strict blocked SPDP rank of the corresponding real
`cookLevinLocalBlockQ`. -/
theorem cookLevinLocalBlockQ_routeBLocalGadget_rank_eq_spdpRank
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi)
    (v : Fin N) :
    ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
      M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank =
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        kappa kappa
        (cookLevinLocalBlockQ M n hn htb hns (data.blockOfVertex v)) := by
  rfl

/-- If a real local block sees fewer than `kappa` variables, then its forgotten
Route B local-gadget rank is zero. -/
theorem cookLevinLocalBlockQ_routeBLocalGadget_rank_eq_zero_of_vars_card_lt_kappa
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi)
    (v : Fin N)
    (hvars :
      (cookLevinLocalBlockQ M n hn htb hns (data.blockOfVertex v)).vars.card <
        kappa) :
    ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
      M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank =
      0 := by
  rw [cookLevinLocalBlockQ_routeBLocalGadget_rank_eq_spdpRank]
  exact
    cookLevinLocalBlockQ_rank_eq_zero_of_vars_card_lt_kappa
      M n hn htb hns kappa kappa (data.blockOfVertex v) hvars

/-- Pointwise obstruction: below support size `kappa`, a real local block
cannot realize the checked pocket-family rank at the same vertex. -/
theorem not_cookLevinLocalBlockQ_realizes_pocket_of_vars_card_lt_kappa
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi)
    (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN) (hkappa : 0 < kappa)
    (hvars :
      (cookLevinLocalBlockQ M n hn htb hns (data.blockOfVertex v)).vars.card <
        kappa) :
    ¬
      ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
        M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank =
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank := by
  intro hrealizes
  have hzero :
      ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
        M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank =
        0 :=
    cookLevinLocalBlockQ_routeBLocalGadget_rank_eq_zero_of_vars_card_lt_kappa
      M n hn htb hns alpha beta alpha0 kappa G chi Phi data v hvars
  have hpocket :
      kappa <= (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank :=
    cookLevinPocketLocalGadget_rank_kappa alpha kappa gadgetN v halpha hgadgetN
  rw [hzero] at hrealizes
  rw [← hrealizes] at hpocket
  omega

/-- Family form: if even one selected real local block has support cardinality
below `kappa`, then no pointwise pocket-rank realization equality can hold for
the entire Route B local-block family. -/
theorem not_forall_cookLevinLocalBlockQ_realizes_pocket_of_exists_vars_card_lt_kappa
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn htb hns alpha beta alpha0 kappa G chi Phi)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN) (hkappa : 0 < kappa)
    (hbad :
      ∃ v : Fin N,
        (cookLevinLocalBlockQ M n hn htb hns (data.blockOfVertex v)).vars.card <
          kappa) :
    ¬
      forall v : Fin N,
        ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
          M n hn htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank =
          (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank := by
  intro hrealizes
  rcases hbad with ⟨v, hvars⟩
  exact
    not_cookLevinLocalBlockQ_realizes_pocket_of_vars_card_lt_kappa
      M n hn htb hns alpha beta alpha0 kappa gadgetN G chi Phi
      data v halpha hgadgetN hkappa hvars (hrealizes v)

/-! ## Axiom audit anchors -/

#print axioms cookLevinLocalBlockQ_routeBLocalGadget_rank_eq_spdpRank
#print axioms cookLevinLocalBlockQ_routeBLocalGadget_rank_eq_zero_of_vars_card_lt_kappa
#print axioms not_cookLevinLocalBlockQ_realizes_pocket_of_vars_card_lt_kappa
#print axioms not_forall_cookLevinLocalBlockQ_realizes_pocket_of_exists_vars_card_lt_kappa

end PallLean.Paper93.Paper283

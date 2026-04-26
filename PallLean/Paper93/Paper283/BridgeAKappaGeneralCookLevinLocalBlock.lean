import PallLean.Paper93.Paper283.BridgeAKappaOneCookLevinLocalBlock

/-!
# Bridge A arbitrary-kappa derivative-row frontier for the real local block

The unconditional real compiler-local theorem currently available is the
`kappa = 1` result in `BridgeAKappaOneCookLevinLocalBlock`.  For paper-scale
`kappa`, the missing mathematical input is not rank bookkeeping: it is a
kernel-checked construction of `kappa` linearly independent strict-`kappa`
derivative rows of the actual local block product
`cookLevinLocalBlockQ`.

This file isolates that remaining input in the smallest useful form.  Given a
`Fin kappa` family of block-admissible derivative lists, each of length
`kappa`, whose projected derivative rows are linearly independent, we prove
the desired arbitrary-`kappa` rank lower bound for the real local block
product.  The theorem is fully kernel checked and introduces no axioms.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-- Generic strict-profile rank lower bound from a linearly independent family
of projected derivative rows. -/
theorem mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows
    {N rowCount kappa ell : Nat}
    (B : BlockPartition N) (p : MvPolynomial (Fin N) Rat)
    (rows : Fin rowCount -> List (Fin N))
    (hlen : forall r : Fin rowCount, (rows r).length = kappa)
    (hadm : forall r : Fin rowCount, isBlockAdmissible B (rows r))
    (hli :
      LinearIndependent Rat
        (fun r : Fin rowCount => mlProj (iterDerivList (rows r) p))) :
    rowCount <= mlBlockedSpdpRank B kappa ell p := by
  classical
  have hmem : forall r : Fin rowCount,
      mlProj (iterDerivList (rows r) p) ∈
        mlBlockedSpdpSubspace B kappa ell p := by
    intro r
    simpa using
      (mlProj_deriv_mem B kappa ell p (rows r) (hlen r) (hadm r))
  unfold mlBlockedSpdpRank
  set row : Fin rowCount -> mlBlockedSpdpSubspace B kappa ell p :=
    fun r => ⟨mlProj (iterDerivList (rows r) p), hmem r⟩ with hrow
  have hli_sub : LinearIndependent Rat row := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i hi
    apply hli s w ?_ i hi
    have hval : (∑ j ∈ s, w j • row j).val =
        (0 : mlBlockedSpdpSubspace B kappa ell p).val :=
      congrArg Subtype.val hw
    simpa [hrow] using hval
  simpa using hli_sub.fintype_card_le_finrank

/-- Arbitrary-`kappa` rank lower bound for the real Cook-Levin local block
product, conditional exactly on a `kappa`-family of independent strict
`kappa` derivative rows. -/
theorem cookLevinLocalBlockQ_rank_ge_of_linearlyIndependent_derivativeRows
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (kappa : Nat)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (rows : Fin kappa -> List (Fin n))
    (hlen : forall r : Fin kappa, (rows r).length = kappa)
    (hadm :
      forall r : Fin kappa,
        isBlockAdmissible
          (cook_levin_compilation M n hn htb hns).partition
          (rows r))
    (hli :
      LinearIndependent Rat
        (fun r : Fin kappa =>
          mlProj (iterDerivList (rows r)
            (cookLevinLocalBlockQ M n hn htb hns b)))) :
    kappa <=
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        kappa kappa
        (cookLevinLocalBlockQ M n hn htb hns b) := by
  exact
    mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows
      (cook_levin_compilation M n hn htb hns).partition
      (cookLevinLocalBlockQ M n hn htb hns b)
      rows hlen hadm hli

/-- Energy-to-rank form of the arbitrary-`kappa` real local-block bridge,
assuming each Route B vertex supplies its own independent strict-`kappa`
derivative-row family for the selected compiler block. -/
theorem cookLevinLocalBlockQEnergyToRankTarget_of_linearlyIndependent_derivativeRows
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockOfVertex :
      Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (rows : Fin N -> Fin kappa -> List (Fin n))
    (hlen : forall (v : Fin N) (r : Fin kappa), (rows v r).length = kappa)
    (hadm :
      forall (v : Fin N) (r : Fin kappa),
        isBlockAdmissible
          (cook_levin_compilation M n hn htb hns).partition
          (rows v r))
    (hli :
      forall v : Fin N,
        LinearIndependent Rat
          (fun r : Fin kappa =>
            mlProj (iterDerivList (rows v r)
              (cookLevinLocalBlockQ M n hn htb hns (blockOfVertex v))))) :
    CookLevinLocalBlockQEnergyToRankTarget
      M n hn htb hns alpha beta alpha0 kappa G chi Phi blockOfVertex := by
  intro v _henergy
  exact
    cookLevinLocalBlockQ_rank_ge_of_linearlyIndependent_derivativeRows
      M n hn htb hns kappa (blockOfVertex v) (rows v)
      (hlen v) (hadm v) (hli v)

/-- Packaged arbitrary-`kappa` Bridge A data for the real local block product,
conditional on independent strict-`kappa` derivative rows at every selected
compiler block. -/
noncomputable def cookLevinLocalBlockQBridgeAData_of_linearlyIndependent_derivativeRows
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockOfVertex :
      Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (rows : Fin N -> Fin kappa -> List (Fin n))
    (hlen : forall (v : Fin N) (r : Fin kappa), (rows v r).length = kappa)
    (hadm :
      forall (v : Fin N) (r : Fin kappa),
        isBlockAdmissible
          (cook_levin_compilation M n hn htb hns).partition
          (rows v r))
    (hli :
      forall v : Fin N,
        LinearIndependent Rat
          (fun r : Fin kappa =>
            mlProj (iterDerivList (rows v r)
              (cookLevinLocalBlockQ M n hn htb hns (blockOfVertex v))))) :
    CookLevinLocalBlockQBridgeAData
      M n hn htb hns alpha beta alpha0 kappa G chi Phi where
  blockOfVertex := blockOfVertex
  energy_to_spdpRank :=
    cookLevinLocalBlockQEnergyToRankTarget_of_linearlyIndependent_derivativeRows
      M n hn htb hns alpha beta alpha0 kappa G chi Phi
      blockOfVertex rows hlen hadm hli

/-! ## Axiom audit anchors -/

#print axioms mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows
#print axioms cookLevinLocalBlockQ_rank_ge_of_linearlyIndependent_derivativeRows
#print axioms cookLevinLocalBlockQEnergyToRankTarget_of_linearlyIndependent_derivativeRows
#print axioms cookLevinLocalBlockQBridgeAData_of_linearlyIndependent_derivativeRows

end PallLean.Paper93.Paper283

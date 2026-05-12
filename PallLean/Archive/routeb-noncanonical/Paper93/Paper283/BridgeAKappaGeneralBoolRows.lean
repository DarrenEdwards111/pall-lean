import PallLean.Paper93.Paper283.BridgeAKappaGeneralCookLevinLocalBlock
import PallLean.Paper93.Paper283.BridgeABlockEvalAtZero

/-!
# Bridge A arbitrary-kappa boolean-row support for the real local block

This file records the strongest general-kappa statement currently available
for derivative rows of the actual real Cook-Levin local block polynomial
`cookLevinLocalBlockQ`.

The checked payload is a coefficient-diagonal criterion: if a family of
strict length-`kappa` derivative rows of the real local block has a diagonal
coefficient witness after `mlProj`, then those rows are linearly independent
and feed the existing arbitrary-`kappa` Bridge A data constructor.

The final lemmas also make explicit a structural obstruction in the preferred
"one block contains kappa variables" formulation: `isBlockAdmissible` permits
at most one derivative variable from each block, so a strict row supported
entirely in one block can have length at most one.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Linear independence from checked coefficient probes -/

/-- A flexible coefficient-diagonal criterion for projected iterated
derivative rows.  The probes may be any monomial exponents; in applications
they are usually chosen from booleanity support monomials. -/
theorem linearIndependent_mlProj_iterDerivList_of_coeff_diagonal
    {N rowCount : Nat} {p : MvPolynomial (Fin N) Rat}
    (rows : Fin rowCount -> List (Fin N))
    (probe : Fin rowCount -> Fin N →₀ Nat)
    (diag : Fin rowCount -> Rat)
    (hdiag_ne : forall r : Fin rowCount, diag r ≠ 0)
    (hcoeff :
      forall r s : Fin rowCount,
        MvPolynomial.coeff (probe r)
            (mlProj (iterDerivList (rows s) p)) =
          if r = s then diag r else 0) :
    LinearIndependent Rat
      (fun r : Fin rowCount => mlProj (iterDerivList (rows r) p)) := by
  classical
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hcoeff_zero :
      MvPolynomial.coeff (probe i)
          (∑ j ∈ s, w j • mlProj (iterDerivList (rows j) p)) = 0 := by
    rw [hw]
    simp
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
    at hcoeff_zero
  have hsum :
      (∑ j ∈ s,
        w j *
          MvPolynomial.coeff (probe i)
            (mlProj (iterDerivList (rows j) p))) =
        w i * diag i := by
    rw [Finset.sum_eq_single i]
    · rw [hcoeff i i, if_pos rfl]
    · intro j _hj hji
      rw [hcoeff i j, if_neg (fun hij => hji hij.symm), mul_zero]
    · intro hnot
      exact (hnot hi).elim
  have hmul_zero : w i * diag i = 0 := hsum ▸ hcoeff_zero
  exact (mul_eq_zero.mp hmul_zero).resolve_right (hdiag_ne i)

/-- Specialization of the coefficient-diagonal criterion to the real
Cook-Levin local block polynomial. -/
theorem linearIndependent_cookLevinLocalBlockQ_derivativeRows_of_coeff_diagonal
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (rowCount : Nat)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (rows : Fin rowCount -> List (Fin n))
    (probe : Fin rowCount -> Fin n →₀ Nat)
    (diag : Fin rowCount -> Rat)
    (hdiag_ne : forall r : Fin rowCount, diag r ≠ 0)
    (hcoeff :
      forall r s : Fin rowCount,
        MvPolynomial.coeff (probe r)
            (mlProj (iterDerivList (rows s)
              (cookLevinLocalBlockQ M n hn htb hns b))) =
          if r = s then diag r else 0) :
    LinearIndependent Rat
      (fun r : Fin rowCount =>
        mlProj (iterDerivList (rows r)
          (cookLevinLocalBlockQ M n hn htb hns b))) := by
  exact
    linearIndependent_mlProj_iterDerivList_of_coeff_diagonal
      rows probe diag hdiag_ne hcoeff

/-- Rank lower bound for the real local block from coefficient-diagonal
projected derivative rows. -/
theorem cookLevinLocalBlockQ_rank_ge_of_coeff_diagonal
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (kappa rowCount : Nat)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (rows : Fin rowCount -> List (Fin n))
    (hlen : forall r : Fin rowCount, (rows r).length = kappa)
    (hadm :
      forall r : Fin rowCount,
        isBlockAdmissible
          (cook_levin_compilation M n hn htb hns).partition
          (rows r))
    (probe : Fin rowCount -> Fin n →₀ Nat)
    (diag : Fin rowCount -> Rat)
    (hdiag_ne : forall r : Fin rowCount, diag r ≠ 0)
    (hcoeff :
      forall r s : Fin rowCount,
        MvPolynomial.coeff (probe r)
            (mlProj (iterDerivList (rows s)
              (cookLevinLocalBlockQ M n hn htb hns b))) =
          if r = s then diag r else 0) :
    rowCount <=
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        kappa kappa
        (cookLevinLocalBlockQ M n hn htb hns b) := by
  exact
    mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows
      (cook_levin_compilation M n hn htb hns).partition
      (cookLevinLocalBlockQ M n hn htb hns b)
      rows hlen hadm
      (linearIndependent_cookLevinLocalBlockQ_derivativeRows_of_coeff_diagonal
        M n hn htb hns rowCount b rows probe diag hdiag_ne hcoeff)

/-! ## Feeding the arbitrary-kappa Bridge A package -/

/-- Energy-to-rank target from coefficient-diagonal strict derivative rows at
each selected real Cook-Levin local block. -/
theorem cookLevinLocalBlockQEnergyToRankTarget_of_coeff_diagonal
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
    (probe : Fin N -> Fin kappa -> Fin n →₀ Nat)
    (diag : Fin N -> Fin kappa -> Rat)
    (hdiag_ne : forall (v : Fin N) (r : Fin kappa), diag v r ≠ 0)
    (hcoeff :
      forall (v : Fin N) (r s : Fin kappa),
        MvPolynomial.coeff (probe v r)
            (mlProj (iterDerivList (rows v s)
              (cookLevinLocalBlockQ M n hn htb hns (blockOfVertex v)))) =
          if r = s then diag v r else 0) :
    CookLevinLocalBlockQEnergyToRankTarget
      M n hn htb hns alpha beta alpha0 kappa G chi Phi blockOfVertex := by
  intro v _henergy
  exact
    cookLevinLocalBlockQ_rank_ge_of_coeff_diagonal
      M n hn htb hns kappa kappa (blockOfVertex v) (rows v)
      (hlen v) (hadm v) (probe v) (diag v) (hdiag_ne v) (hcoeff v)

/-- Packaged arbitrary-`kappa` Bridge A data for the real local block product
from coefficient-diagonal strict derivative rows at every selected compiler
block. -/
noncomputable def cookLevinLocalBlockQBridgeAData_of_coeff_diagonal
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
    (probe : Fin N -> Fin kappa -> Fin n →₀ Nat)
    (diag : Fin N -> Fin kappa -> Rat)
    (hdiag_ne : forall (v : Fin N) (r : Fin kappa), diag v r ≠ 0)
    (hcoeff :
      forall (v : Fin N) (r s : Fin kappa),
        MvPolynomial.coeff (probe v r)
            (mlProj (iterDerivList (rows v s)
              (cookLevinLocalBlockQ M n hn htb hns (blockOfVertex v)))) =
          if r = s then diag v r else 0) :
    CookLevinLocalBlockQBridgeAData
      M n hn htb hns alpha beta alpha0 kappa G chi Phi where
  blockOfVertex := blockOfVertex
  energy_to_spdpRank :=
    cookLevinLocalBlockQEnergyToRankTarget_of_coeff_diagonal
      M n hn htb hns alpha beta alpha0 kappa G chi Phi
      blockOfVertex rows hlen hadm probe diag hdiag_ne hcoeff

/-! ## Single-block obstruction for strict admissible rows -/

/-- A block-admissible list supported entirely inside one block has length at
most one. -/
theorem length_le_one_of_blockAdmissible_all_assign_eq
    {N : Nat} {B : BlockPartition N} {S : List (Fin N)}
    {b : Fin B.numBlocks}
    (hadm : isBlockAdmissible B S)
    (hall : forall v : Fin N, v ∈ S -> B.assign v = b) :
    S.length <= 1 := by
  classical
  have hfilter : S.filter (fun v => B.assign v = b) = S := by
    apply List.filter_eq_self.mpr
    intro v hv
    exact decide_eq_true (hall v hv)
  simpa [hfilter] using hadm.2 b

/-- Therefore a strict length-`kappa` admissible row supported in one block
forces `kappa <= 1`. -/
theorem kappa_le_one_of_blockAdmissible_row_supported_in_single_block
    {N kappa : Nat} {B : BlockPartition N} {S : List (Fin N)}
    {b : Fin B.numBlocks}
    (hlen : S.length = kappa)
    (hadm : isBlockAdmissible B S)
    (hall : forall v : Fin N, v ∈ S -> B.assign v = b) :
    kappa <= 1 := by
  simpa [hlen] using
    (length_le_one_of_blockAdmissible_all_assign_eq
      (B := B) (S := S) (b := b) hadm hall)

/-- Finset form of the same obstruction: distinct variables from a single
block cannot form a block-admissible derivative row of cardinality above one.
-/
theorem card_le_one_of_blockAdmissible_toList_supported_in_single_block
    {N : Nat} {B : BlockPartition N} (S : Finset (Fin N))
    {b : Fin B.numBlocks}
    (hadm : isBlockAdmissible B S.toList)
    (hall : forall v : Fin N, v ∈ S -> B.assign v = b) :
    S.card <= 1 := by
  have hlen : S.toList.length = S.card := Finset.length_toList S
  exact
    kappa_le_one_of_blockAdmissible_row_supported_in_single_block
      (B := B) (S := S.toList) (b := b) hlen hadm
      (by
        intro v hv
        exact hall v (by simpa using hv))

/-! ## Axiom audit anchors -/

#print axioms linearIndependent_mlProj_iterDerivList_of_coeff_diagonal
#print axioms linearIndependent_cookLevinLocalBlockQ_derivativeRows_of_coeff_diagonal
#print axioms cookLevinLocalBlockQ_rank_ge_of_coeff_diagonal
#print axioms cookLevinLocalBlockQEnergyToRankTarget_of_coeff_diagonal
#print axioms cookLevinLocalBlockQBridgeAData_of_coeff_diagonal
#print axioms length_le_one_of_blockAdmissible_all_assign_eq
#print axioms kappa_le_one_of_blockAdmissible_row_supported_in_single_block
#print axioms card_le_one_of_blockAdmissible_toList_supported_in_single_block

end PallLean.Paper93.Paper283

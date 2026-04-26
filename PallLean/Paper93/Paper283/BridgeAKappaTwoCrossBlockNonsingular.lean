import PallLean.Paper93.Paper283.BridgeAKappaTwoFourFamilyComputation
import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockProbe
import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockConcrete
import PallLean.Paper93.Paper283.BridgeAKappaTwoBoolOnly
import PallLean.Paper93.Paper283.BridgeAKappaTwoCookLevinLocalBlock
import PallLean.Paper93.Paper283.BridgeAKappaGeneralBoolRows
import PallLean.Paper93.Paper283.BridgeAKappaGeneralCookLevinLocalBlock
import PallLean.IterDerivHelpers

/-!
# Closing κ = 2 Bridge A on `cookLevinLocalBlockQ` via a nonsingular 2×2 matrix

This file completes the κ = 2 cross-block Bridge A target on the real
Cook-Levin local block product `cookLevinLocalBlockQ` by replacing the
overly strict *diagonal* certificate of
`BridgeAKappaTwoCookLevinLocalBlock`
(`CookLevinLocalBlockQKappaTwoCrossBlockDiagonal`) by a strictly more
general *nonsingular* certificate that accepts any 2×2 cross-row
coefficient matrix with nonzero determinant.

## Why generalise?

The four-family path enumeration in `BridgeAKappaTwoFourFamilyComputation`
(commit `97daa11`) shows that for the natural cross-block rows
`rowRight = [3k+2, 3k+3]` and `rowLeft = [3k-1, 3k]` together with the
natural monomial probes `probeRight = X_{3k+1}·X_{3k+2}` and
`probeLeft = X_{3k}·X_{3k+1}`, the cross-row coefficient matrix has the
non-Kronecker shape

```
      ⎡ 2 K   K  ⎤
M_K = ⎣  K   2 K ⎦      with  K = (1 + Σ_q c_q) · (Σ_q c_q) > 0,
```

i.e. it is *not diagonal* (so `kappaTwoCrossBlockMonomialProbeDiagonality`
cannot hold) but its determinant is `det M_K = 4K² − K² = 3 K² ≠ 0`,
proven kernel-only as `crossBlockExpectedCoeffMatrix_det = 3 K²`.

The diagonal certificate of `dc1bc76` is therefore strictly stronger
than what the actual algebra of `cookLevinLocalBlockQ` provides at the
chosen probe pair.  The correct, sharper criterion is
*non-singularity* of the 2×2 cross-row coefficient matrix.

## What this file does

1. **Generalised certificate type.**  We expose
   `CookLevinLocalBlockQKappaTwoCrossBlockNonsingular`, a sibling
   structure of `CookLevinLocalBlockQKappaTwoCrossBlockDiagonal` that
   takes:
     * two strict length-2 cross-block-admissible derivative rows;
     * two probe finsupp exponent vectors;
     * the four cross-row coefficient values
       `(m_rs)_{r,s ∈ Fin 2}` together with the four equalities
       `coeff(probe r, mlProj(iterDerivList rows_s Q_b)) = m_rs`;
     * a single `det = m_00·m_11 − m_01·m_10 ≠ 0` non-singularity
       hypothesis.

2. **Generalised rank lower bound.**  We prove
   `cookLevinLocalBlockQ_rank_two_le_of_crossBlockNonsingular`:
   any such certificate yields the rank lower bound
   `2 ≤ mlBlockedSpdpRank · · · 2 2 (cookLevinLocalBlockQ M n hn htb hns b)`.
   The proof composes
   `linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular`
   (the kernel-only generic 2×2 nonsingular linear-independence lemma
   from `BridgeAKappaTwoBoolOnly`, commit `8acefdc`) with
   `mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows`.

3. **Concrete instance via the `K`-matrix.**  We supply
   `crossBlockNonsingular_of_K_matrix`, a constructor that takes the
   precise four coefficient identities

   ```
   coeff(probeRight, ∂_rowRight Q) = 2K,   coeff(probeRight, ∂_rowLeft Q) =  K,
   coeff(probeLeft , ∂_rowRight Q) =  K,   coeff(probeLeft , ∂_rowLeft Q) = 2K,
   ```

   and the positivity hypothesis `0 < K`, and produces the
   `CookLevinLocalBlockQKappaTwoCrossBlockNonsingular` package.  The
   non-singularity discharge uses
   `crossBlockExpectedCoeffMatrix_det_ne_zero` (commit `97daa11`).

4. **End-to-end conditional theorem.**  We package the κ = 2 closure
   on the real Cook-Levin local block at an interior locality block
   into the named theorem
   `cookLevinLocalBlockQ_rank_two_le_real`, which states the rank
   lower bound conditional on the residual four-family coefficient
   identities and `0 < K`.

## Status: end-to-end κ = 2 closure modulo the residual coefficient
identity

This file collapses the κ = 2 closure obstruction down to a single,
finite, type-level monomial-coefficient identity at the two-fold
derivative of `Q_b` together with the elementary positivity
`(1 + Σ_q c_q)(Σ_q c_q) > 0` (which follows from
`numStates ≥ 1` since each `transCoeff M q ≥ 1`).  The diagonal-only
form was the structural blocker; with this generalisation, the
`κ = 2` Bridge A target on `cookLevinLocalBlockQ` is closed at the
type level by the sequence

```
{four coefficient identities}  +  {0 < K}
   ⟹  CookLevinLocalBlockQKappaTwoCrossBlockNonsingular
   ⟹  2 ≤ mlBlockedSpdpRank ⋯ (cookLevinLocalBlockQ ⋯).
```

No new axioms are introduced.  The kernel-only set
`[propext, Classical.choice, Quot.sound]` is preserved.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: cross-block row construction (mirror of dc1bc76 / 901b8ca)

The cross-block rows constructed in `BridgeAKappaTwoCrossBlockConcrete`
and re-exposed in `BridgeAKappaTwoCrossBlockProbe` are file-private to
each.  We mirror them here so the new nonsingular package can refer to
them locally.  These definitions are deliberately defeq to the ones in
the earlier files. -/

/-- A `Fin n` index `3k + r` for `r < 3` and `3k + r < n`. -/
private def nsVarIdx (n k r : Nat) (h : 3 * k + r < n) : Fin n :=
  ⟨3 * k + r, h⟩

/-- The right-boundary cross-block row `[3k+2, 3k+3]`. -/
private noncomputable def nsRowRight (n k : Nat)
    (hk : 3 * k + 3 < n) : List (Fin n) :=
  [nsVarIdx n k 2 (by omega),
   nsVarIdx n k 3 hk]

/-- The left-boundary cross-block row `[3k-1, 3k]`. -/
private noncomputable def nsRowLeft (n k : Nat)
    (hk1 : 1 ≤ k) (hk2 : 3 * k < n) : List (Fin n) :=
  [nsVarIdx n (k - 1) 2 (by
      have heq : 3 * (k - 1) + 3 = 3 * k := by
        rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
        congr 1; omega
      omega),
   nsVarIdx n k 0 (by omega)]

/-- Length of the right row is 2. -/
private theorem nsRowRight_length (n k : Nat) (hk : 3 * k + 3 < n) :
    (nsRowRight n k hk).length = 2 := by
  unfold nsRowRight; simp

/-- Length of the left row is 2. -/
private theorem nsRowLeft_length (n k : Nat)
    (hk1 : 1 ≤ k) (hk2 : 3 * k < n) :
    (nsRowLeft n k hk1 hk2).length = 2 := by
  unfold nsRowLeft; simp

/-- The locality block of an interior index `k`. -/
private def nsInteriorBlock
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk : 3 * k + 3 < n) :
    Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks :=
  ⟨k, by
    rw [cook_levin_numBlocks]
    omega⟩

/-! ## Section B: row admissibility (mirror of the proofs in 901b8ca). -/

private theorem ns_assign_varIdx
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k r : Nat) (h : 3 * k + r < n) (hr : r < 3) :
    ((cook_levin_compilation M n hn htb hns).partition.assign
        (nsVarIdx n k r h)).val = k := by
  rw [cook_levin_assign]
  show (3 * k + r) / 3 = k
  have hquot : (3 * k + r) / 3 = k + r / 3 := by
    have := Nat.mul_add_div (by decide : 0 < 3) k r
    omega
  rw [hquot]
  have : r / 3 = 0 := Nat.div_eq_of_lt hr
  omega

private theorem nsRowRight_admissible
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk : 3 * k + 3 < n) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition
      (nsRowRight n k hk) := by
  classical
  unfold nsRowRight
  set v1 : Fin n := nsVarIdx n k 2 (by omega)
  set v2 : Fin n := nsVarIdx n k 3 hk
  have hassign1 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v1).val = k :=
    ns_assign_varIdx M n hn htb hns k 2 (by omega) (by decide)
  have hassign2 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v2).val = k + 1 := by
    rw [cook_levin_assign]
    show (3 * k + 3) / 3 = k + 1
    rw [show (3 * k + 3 : Nat) = 3 * (k + 1) from by ring,
      Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  refine ⟨?_, ?_⟩
  · rw [List.nodup_cons]
    refine ⟨?_, by simp⟩
    intro h
    simp at h
    have hv : v1 = v2 := h
    have hval : v1.val = v2.val := Fin.val_eq_of_eq hv
    show False
    simp [v1, v2, nsVarIdx] at hval
  · intro b
    show (([v1, v2]).filter
        (fun i =>
          (cook_levin_compilation M n hn htb hns).partition.assign i = b)).length ≤ 1
    by_cases h1 : (cook_levin_compilation M n hn htb hns).partition.assign v1 = b
    · have h2_ne :
          (cook_levin_compilation M n hn htb hns).partition.assign v2 ≠ b := by
        intro hcontra
        have hb_eq_k : b.val = k := (Fin.val_eq_of_eq h1).symm.trans hassign1
        have hb_eq_k1 : b.val = k + 1 :=
          (Fin.val_eq_of_eq hcontra).symm.trans hassign2
        omega
      rw [List.filter_cons_of_pos (by simpa using h1),
        List.filter_cons_of_neg (by simpa using h2_ne)]
      simp
    · rw [List.filter_cons_of_neg (by simpa using h1)]
      by_cases h2 : (cook_levin_compilation M n hn htb hns).partition.assign v2 = b
      · rw [List.filter_cons_of_pos (by simpa using h2)]; simp
      · rw [List.filter_cons_of_neg (by simpa using h2)]; simp

private theorem nsRowLeft_admissible
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k < n) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition
      (nsRowLeft n k hk1 hk2) := by
  classical
  unfold nsRowLeft
  have hk0 : 3 * (k - 1) + 2 < n := by
    have h1 : 3 * (k - 1) + 3 = 3 * k := by
      rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]; congr 1; omega
    omega
  set v1 : Fin n := nsVarIdx n (k - 1) 2 hk0
  set v2 : Fin n := nsVarIdx n k 0 (by omega)
  have hassign1 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v1).val = k - 1 :=
    ns_assign_varIdx M n hn htb hns (k - 1) 2 hk0 (by decide)
  have hassign2 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v2).val = k :=
    ns_assign_varIdx M n hn htb hns k 0 (by omega) (by decide)
  refine ⟨?_, ?_⟩
  · rw [List.nodup_cons]
    refine ⟨?_, by simp⟩
    intro h
    simp at h
    have hv : v1 = v2 := h
    have hval : v1.val = v2.val := Fin.val_eq_of_eq hv
    show False
    simp [v1, v2, nsVarIdx] at hval
    omega
  · intro b
    show (([v1, v2]).filter
        (fun i =>
          (cook_levin_compilation M n hn htb hns).partition.assign i = b)).length ≤ 1
    by_cases h1 : (cook_levin_compilation M n hn htb hns).partition.assign v1 = b
    · have h2_ne :
          (cook_levin_compilation M n hn htb hns).partition.assign v2 ≠ b := by
        intro hcontra
        have hb_eq_k1 : b.val = k - 1 :=
          (Fin.val_eq_of_eq h1).symm.trans hassign1
        have hb_eq_k : b.val = k :=
          (Fin.val_eq_of_eq hcontra).symm.trans hassign2
        omega
      rw [List.filter_cons_of_pos (by simpa using h1),
        List.filter_cons_of_neg (by simpa using h2_ne)]
      simp
    · rw [List.filter_cons_of_neg (by simpa using h1)]
      by_cases h2 : (cook_levin_compilation M n hn htb hns).partition.assign v2 = b
      · rw [List.filter_cons_of_pos (by simpa using h2)]; simp
      · rw [List.filter_cons_of_neg (by simpa using h2)]; simp

/-! ## Section C: the nonsingular cross-block certificate type

The generalised certificate accepts any 2×2 cross-row coefficient
matrix with nonzero determinant.  This is strictly weaker than the
diagonal certificate of `dc1bc76` and is the precise shape produced by
the four-family path enumeration of commit `97daa11`. -/

/-- The `kappa = 2` cross-block *nonsingular* certificate for the real
Cook-Levin local block product.

This certificate generalises
`CookLevinLocalBlockQKappaTwoCrossBlockDiagonal`: instead of requiring
the cross-row coefficient matrix to be diagonal, it requires only that
the matrix `(m_rs) = coeff(probe r, mlProj(iterDerivList rows s Q_b))`
have nonzero determinant.

Once the four matrix entries are witnessed and the determinant is
nonzero, the linear-independence-from-nonsingular-2×2 lemma
`linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular`
(commit `8acefdc`) and the generic
`mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows`
combine to deliver the rank lower bound. -/
structure CookLevinLocalBlockQKappaTwoCrossBlockNonsingular
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    : Type where
  rows  : Fin 2 → List (Fin n)
  probe : Fin 2 → Fin n →₀ Nat
  m00   : Rat
  m01   : Rat
  m10   : Rat
  m11   : Rat
  hlen  : ∀ r : Fin 2, (rows r).length = 2
  hadm  :
    ∀ r : Fin 2,
      isBlockAdmissible
        (cook_levin_compilation M n hn htb hns).partition (rows r)
  hm00  :
    MvPolynomial.coeff (probe 0)
        (mlProj (iterDerivList (rows 0)
          (cookLevinLocalBlockQ M n hn htb hns b))) = m00
  hm01  :
    MvPolynomial.coeff (probe 0)
        (mlProj (iterDerivList (rows 1)
          (cookLevinLocalBlockQ M n hn htb hns b))) = m01
  hm10  :
    MvPolynomial.coeff (probe 1)
        (mlProj (iterDerivList (rows 0)
          (cookLevinLocalBlockQ M n hn htb hns b))) = m10
  hm11  :
    MvPolynomial.coeff (probe 1)
        (mlProj (iterDerivList (rows 1)
          (cookLevinLocalBlockQ M n hn htb hns b))) = m11
  hdet  : m00 * m11 - m01 * m10 ≠ 0

/-! ## Section D: rank lower bound from a nonsingular cross-block
certificate.

We compose:

* `linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular`
  (8acefdc): nonsingular 2×2 ⇒ linear independence.
* `mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows`: linear
  independence of length-2 admissible rows ⇒ rank ≥ 2.

This composition replaces the diagonal-only path of `dc1bc76`. -/

/-- Linear independence of the two projected derivative rows from a
nonsingular cross-block certificate.  Pure composition of
`linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular`
with the four matrix-entry hypotheses. -/
theorem linearIndependent_of_crossBlockNonsingular
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (data :
      CookLevinLocalBlockQKappaTwoCrossBlockNonsingular
        M n hn htb hns b) :
    LinearIndependent Rat
      (fun r : Fin 2 =>
        mlProj (iterDerivList (data.rows r)
          (cookLevinLocalBlockQ M n hn htb hns b))) := by
  refine
    linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular
      (p := cookLevinLocalBlockQ M n hn htb hns b)
      data.rows data.probe ?_
  -- Substitute the four hypotheses into the determinant non-vanishing.
  simp only [data.hm00, data.hm01, data.hm10, data.hm11]
  exact data.hdet

/-- Conditional `kappa = 2` rank lower bound for the real Cook-Levin
local block product, packaged from a *nonsingular* cross-block
certificate.

This is the sibling of
`cookLevinLocalBlockQ_rank_two_le_of_crossBlockDiagonal` for the
strictly more permissive non-singularity criterion. -/
theorem cookLevinLocalBlockQ_rank_two_le_of_crossBlockNonsingular
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (data :
      CookLevinLocalBlockQKappaTwoCrossBlockNonsingular
        M n hn htb hns b) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns b) := by
  exact
    mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows
      (cook_levin_compilation M n hn htb hns).partition
      (cookLevinLocalBlockQ M n hn htb hns b)
      data.rows data.hlen data.hadm
      (linearIndependent_of_crossBlockNonsingular
        M n hn htb hns b data)

/-! ## Section E: building the `K`-matrix instance from
`97daa11`'s `crossBlockExpectedCoeffMatrix_det = 3 K²`

We construct the concrete `CookLevinLocalBlockQKappaTwoCrossBlockNonsingular`
package for the cross-block rows
`rowRight = [3k+2, 3k+3]` and `rowLeft = [3k-1, 3k]`, given:

* `K : Rat` with `0 < K` (the rational invariant of `97daa11`'s
  four-family computation; concretely
  `K = (1 + Σ_q transCoeff M q) · (Σ_q transCoeff M q) > 0`);
* the four coefficient identities matching the
  `crossBlockExpectedCoeffMatrix K` shape `[[2K, K], [K, 2K]]`.

The non-singularity hypothesis is discharged by
`crossBlockExpectedCoeffMatrix_det_ne_zero` from `97daa11`. -/

/-- The concrete `K`-matrix nonsingular cross-block certificate.

Inputs (per the `97daa11` four-family closed form):

* `K : Rat` with `0 < K`.
* The four coefficient identities at the chosen probes
  `probeRight = X_{3k+1}·X_{3k+2}` and `probeLeft = X_{3k}·X_{3k+1}`
  (mirrored from `BridgeAKappaTwoCrossBlockProbe`).
* The two cross-block rows `nsRowRight`, `nsRowLeft` mirrored from
  `BridgeAKappaTwoCrossBlockConcrete`/`BridgeAKappaTwoCrossBlockProbe`.

Output: a full `CookLevinLocalBlockQKappaTwoCrossBlockNonsingular`
package, whose non-singularity discharge uses
`crossBlockExpectedCoeffMatrix_det_ne_zero` to convert
`0 < K` to `2K · 2K − K · K = 3K² ≠ 0`. -/
noncomputable def crossBlockNonsingular_of_K_matrix
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (K : Rat) (hKpos : 0 < K)
    (probe : Fin 2 → Fin n →₀ Nat)
    (h00 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList (nsRowRight n k hk2)
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = 2 * K)
    (h01 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList
            (nsRowLeft n k hk1 (by omega : 3 * k < n))
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = K)
    (h10 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList (nsRowRight n k hk2)
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = K)
    (h11 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList
            (nsRowLeft n k hk1 (by omega : 3 * k < n))
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = 2 * K) :
    CookLevinLocalBlockQKappaTwoCrossBlockNonsingular
      M n hn htb hns
      (nsInteriorBlock M n hn htb hns k hk2) where
  rows := fun r =>
    ![nsRowRight n k hk2,
      nsRowLeft n k hk1 (by omega : 3 * k < n)] r
  probe := probe
  m00 := 2 * K
  m01 := K
  m10 := K
  m11 := 2 * K
  hlen := by
    intro r
    fin_cases r
    · exact nsRowRight_length n k hk2
    · exact nsRowLeft_length n k hk1 (by omega)
  hadm := by
    intro r
    fin_cases r
    · exact nsRowRight_admissible M n hn htb hns k hk2
    · exact nsRowLeft_admissible M n hn htb hns k hk1 (by omega)
  hm00 := by simpa using h00
  hm01 := by simpa using h01
  hm10 := by simpa using h10
  hm11 := by simpa using h11
  hdet := by
    -- (2K) * (2K) - K * K = 3K² ≠ 0  via crossBlockExpectedCoeffMatrix_det_ne_zero.
    have hK_ne : K ≠ 0 := ne_of_gt hKpos
    have hexp := crossBlockExpectedCoeffMatrix_det_ne_zero K hK_ne
    -- Unfold the expected matrix to the explicit four entries 2K, K, K, 2K.
    have heval :
        (crossBlockExpectedCoeffMatrix K 0 0 *
            crossBlockExpectedCoeffMatrix K 1 1) -
          (crossBlockExpectedCoeffMatrix K 0 1 *
            crossBlockExpectedCoeffMatrix K 1 0) =
        (2 * K) * (2 * K) - K * K := by
      unfold crossBlockExpectedCoeffMatrix
      rfl
    rw [heval] at hexp
    exact hexp

/-- End-to-end conditional `κ = 2` rank lower bound on the real
Cook-Levin local block product at an interior locality block,
parameterised by the four `K`-matrix coefficient identities of the
four-family path enumeration.

This is the headline named theorem of this file:

```
2 ≤ mlBlockedSpdpRank (cook_levin_partition) 2 2
      (cookLevinLocalBlockQ M n hn htb hns
        (nsInteriorBlock M n hn htb hns k hk2)).
```

The hypotheses are:

* paper-scale Cook-Levin compiler bounds (`hn`, `htb`, `hns`);
* an interior locality block index `k` with `1 ≤ k` and `3k+3 < n`;
* the rational invariant `K > 0` (delivered by
  `crossBlockKValue_pos_of_pos` once `Σ_q transCoeff M q > 0`);
* a probe pair `probe : Fin 2 → Fin n →₀ Nat`;
* four monomial-coefficient identities expressing that the
  cross-row coefficient matrix at the chosen probes has the shape
  `[[2K, K], [K, 2K]]`. -/
theorem cookLevinLocalBlockQ_rank_two_le_real
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (K : Rat) (hKpos : 0 < K)
    (probe : Fin 2 → Fin n →₀ Nat)
    (h00 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList (nsRowRight n k hk2)
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = 2 * K)
    (h01 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList
            (nsRowLeft n k hk1 (by omega : 3 * k < n))
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = K)
    (h10 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList (nsRowRight n k hk2)
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = K)
    (h11 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList
            (nsRowLeft n k hk1 (by omega : 3 * k < n))
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) = 2 * K) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          (nsInteriorBlock M n hn htb hns k hk2)) := by
  exact
    cookLevinLocalBlockQ_rank_two_le_of_crossBlockNonsingular
      M n hn htb hns
      (nsInteriorBlock M n hn htb hns k hk2)
      (crossBlockNonsingular_of_K_matrix
        M n hn htb hns k hk1 hk2 K hKpos probe h00 h01 h10 h11)

/-! ## Section F: structural bridge from a `crossBlockKValue`-shaped K

The `K` invariant of `97daa11` is `crossBlockKValue S = (1 + S) · S`
which is positive whenever `S > 0`.  In the real Cook-Levin compiler,
`S = Σ_q transCoeff M q ≥ M.numStates ≥ 1 > 0`, so the positivity
hypothesis `0 < K` is automatic at paper scale.  We expose this as a
convenience reduction. -/

/-- Convenience reduction: starting from `0 < S`, the rational
`K = crossBlockKValue S = (1 + S) · S` is strictly positive, hence
nonzero, and the rank lower bound applies. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_of_K_value
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (S : Rat) (hSpos : 0 < S)
    (probe : Fin 2 → Fin n →₀ Nat)
    (h00 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList (nsRowRight n k hk2)
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) =
        2 * crossBlockKValue S)
    (h01 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList
            (nsRowLeft n k hk1 (by omega : 3 * k < n))
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) =
        crossBlockKValue S)
    (h10 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList (nsRowRight n k hk2)
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) =
        crossBlockKValue S)
    (h11 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList
            (nsRowLeft n k hk1 (by omega : 3 * k < n))
            (cookLevinLocalBlockQ M n hn htb hns
              (nsInteriorBlock M n hn htb hns k hk2)))) =
        2 * crossBlockKValue S) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          (nsInteriorBlock M n hn htb hns k hk2)) := by
  have hKpos : 0 < crossBlockKValue S :=
    crossBlockKValue_pos_of_pos hSpos
  exact
    cookLevinLocalBlockQ_rank_two_le_real
      M n hn htb hns k hk1 hk2 (crossBlockKValue S) hKpos
      probe h00 h01 h10 h11

/-! ## Axiom audit anchors -/

#print axioms nsRowRight_length
#print axioms nsRowLeft_length
#print axioms nsRowRight_admissible
#print axioms nsRowLeft_admissible
#print axioms linearIndependent_of_crossBlockNonsingular
#print axioms cookLevinLocalBlockQ_rank_two_le_of_crossBlockNonsingular
#print axioms crossBlockNonsingular_of_K_matrix
#print axioms cookLevinLocalBlockQ_rank_two_le_real
#print axioms cookLevinLocalBlockQ_rank_two_le_real_of_K_value

end PallLean.Paper93.Paper283

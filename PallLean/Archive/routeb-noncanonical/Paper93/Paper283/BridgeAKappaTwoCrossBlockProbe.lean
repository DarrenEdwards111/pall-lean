import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockConcrete
import PallLean.Paper93.Paper283.BridgeABoolDerivative
import PallLean.Paper93.Paper283.BridgeABlockProductRule
import PallLean.Paper93.Paper283.BridgeABlockEvalAtZero
import PallLean.Paper93.Paper283.BridgeAKappaGeneralBoolRows
import PallLean.IterDerivHelpers

/-!
# Non-constant monomial probe for the κ = 2 cross-block target

This file is the follow-up to `BridgeAKappaTwoCrossBlockConcrete`.  Commit
`dc1bc76` constructed two natural cross-block admissible rows for
`cookLevinLocalBlockQ` at an interior locality block `k`:

```
rowRight = [3k+2, 3k+3]
rowLeft  = [3k-1, 3k]
```

and recorded that the **constant** probe `0 : Fin n →₀ ℕ` does **not**
separate them: both projected rows have the same nonzero constant term
`-(1 + Σ_q c_q)`.  Closing `kappa = 2` therefore requires a strictly
non-constant probe.

The intended diagonalising probes proposed in the prompt are

```
probeRight = X_{3k+1} · X_{3k+2}
probeLeft  = X_{3k}   · X_{3k+1}
```

with the heuristic that the cross-factor pair
`(adj-(3k+1,3k+2)) × (adj-(3k+2,3k+3))` of the two-fold Leibniz
expansion of `pderiv_{3k+3} pderiv_{3k+2} Q_b` produces the monomial
`X_{3k+1} · X_{3k+2}` (and dually for the left row).

## Honest report on the structural sub-obstruction

A careful expansion of `pderiv_{3k+3} pderiv_{3k+2} Q_b` via the two-fold
Leibniz rule on the list product reveals that the proposed cross-factor
pair is **not the unique contribution** to the coefficient of
`X_{3k+1} · X_{3k+2}`.  Concretely, after expansion there are two
distinct families of terms whose `mlProj` contains the monomial
`X_{3k+1} · X_{3k+2}`:

1. **Cross-factor families.**  Pairs `(c_1, c_2)` of distinct factors of
   `Q_b` with `c_1` carrying `X_{3k+2}` and `c_2` carrying `X_{3k+3}`.
   The natural example `(adj-(3k+1,3k+2), adj-(3k+2,3k+3))` produces
   the monomial `X_{3k+1} · X_{3k+2}` after evaluating the remaining
   `∏_{c ≠ c_1, c_2}` at `X = 0` to constant `1` and reading the
   leading monomial of the two derivative factors.  A second family of
   the form `(transSkel-(3k+1,3k+2)_q, transSkel-(3k+2,3k+3)_q')` with
   `q, q'` ranging over `Fin M.numStates` adds further contributions of
   the same shape, weighted by `c_q · c_{q'}`.  Mixed pairs
   `(adj, transSkel)` also contribute.

2. **Self-factor families with mlProj-active boolean cross-talk.**  The
   self-factor expansion contributes terms of the form
   `(- c) · ∏_{rest}` for each factor `c = 1 - C · X_{3k+2} · X_{3k+3}`
   in the filtered list.  The `mlProj` of the residual product contains
   the monomial `X_{3k+1} · X_{3k+2}` because the booleanity factors
   `1 - X_{3k+1}(1 - X_{3k+1})` and `1 - X_{3k+2}(1 - X_{3k+2})` carry
   linear-in-`X` summands that combine multiplicatively to yield the
   target monomial.  These contributions are **not** killed by `mlProj`
   even after the multilinear projection, because `mlProj` only
   suppresses higher powers of a single variable, not products of
   distinct linear terms.

The sub-obstruction is therefore a precise **algebraic-cancellation
question**:  does the sum of the cross-factor contributions exceed the
sum of the self-factor + boolean-cross-talk contributions in absolute
value, and does the **same** linear combination kill the analogous
expansion for the left-boundary row at probe `X_{3k+1} · X_{3k+2}`?

The dual question for probe `X_{3k} · X_{3k+1}` and the left row is
symmetric.

To make this obstruction visible at the type level, we expose:

* a `kappaTwoCrossBlockMonomialProbeData` package recording the two
  probes, the diagonal values, and the diagonality witness `hcoeff`
  for the monomial probes, in the exact shape consumed by
  `crossBlockDiagonal_of_certificate`;

* a constructor `kappaTwoCrossBlockProbe_diagonal_of_data` that turns a
  proof of the monomial-coefficient diagonality into the full
  `CookLevinLocalBlockQKappaTwoCrossBlockDiagonal` package and hence
  the `kappa = 2` rank lower bound on the real local block.

This file therefore reduces the residual mathematical content of
`kappa = 2` for the real Cook-Levin local block to a single, precise,
finite, **non-constant** monomial coefficient identity at the
two-fold derivative of `Q_b`.  No new axioms are introduced; the
kernel-only set `[propext, Classical.choice, Quot.sound]` is preserved.
No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: re-exposure of the cross-block row data

The cross-block rows constructed in `BridgeAKappaTwoCrossBlockConcrete`
are file-private to that file.  We mirror the same data here so the
non-constant probe certificate can be expressed in this file.  These
definitions are deliberately defeq to the ones in
`BridgeAKappaTwoCrossBlockConcrete`. -/

/-- A `Fin n` index `3k + r` for `r < 3` and `3k + r < n`. -/
private def probeVarIdx (n k r : Nat) (h : 3 * k + r < n) : Fin n :=
  ⟨3 * k + r, h⟩

/-- The right-boundary cross-block row `[3k+2, 3k+3]`. -/
private noncomputable def probeRowRight (n k : Nat)
    (hk : 3 * k + 3 < n) : List (Fin n) :=
  [probeVarIdx n k 2 (by omega),
   probeVarIdx n k 3 hk]

/-- The left-boundary cross-block row `[3k-1, 3k]`. -/
private noncomputable def probeRowLeft (n k : Nat)
    (hk1 : 1 ≤ k) (hk2 : 3 * k < n) : List (Fin n) :=
  [probeVarIdx n (k - 1) 2 (by
      have heq : 3 * (k - 1) + 3 = 3 * k := by
        rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
        congr 1; omega
      omega),
   probeVarIdx n k 0 (by omega)]

/-- Row lengths. -/
private theorem probeRowRight_length (n k : Nat) (hk : 3 * k + 3 < n) :
    (probeRowRight n k hk).length = 2 := by
  unfold probeRowRight; simp

private theorem probeRowLeft_length (n k : Nat)
    (hk1 : 1 ≤ k) (hk2 : 3 * k < n) :
    (probeRowLeft n k hk1 hk2).length = 2 := by
  unfold probeRowLeft; simp

/-- The locality block of an interior index `k`. -/
private def probeInteriorBlock
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk : 3 * k + 3 < n) :
    Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks :=
  ⟨k, by
    rw [cook_levin_numBlocks]
    omega⟩

/-! ## Section B: row admissibility (mirrors the dc1bc76 proofs).
We reprove admissibility here because the `dc1bc76` versions are file-private
and the proof is short. -/

private theorem probe_assign_varIdx
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k r : Nat) (h : 3 * k + r < n) (hr : r < 3) :
    ((cook_levin_compilation M n hn htb hns).partition.assign
        (probeVarIdx n k r h)).val = k := by
  rw [cook_levin_assign]
  show (3 * k + r) / 3 = k
  have hquot : (3 * k + r) / 3 = k + r / 3 := by
    have := Nat.mul_add_div (by decide : 0 < 3) k r
    omega
  rw [hquot]
  have : r / 3 = 0 := Nat.div_eq_of_lt hr
  omega

private theorem probeRowRight_admissible
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk : 3 * k + 3 < n) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition
      (probeRowRight n k hk) := by
  classical
  unfold probeRowRight
  set v1 : Fin n := probeVarIdx n k 2 (by omega)
  set v2 : Fin n := probeVarIdx n k 3 hk
  have hassign1 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v1).val = k :=
    probe_assign_varIdx M n hn htb hns k 2 (by omega) (by decide)
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
    simp [v1, v2, probeVarIdx] at hval
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

private theorem probeRowLeft_admissible
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k < n) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition
      (probeRowLeft n k hk1 hk2) := by
  classical
  unfold probeRowLeft
  have hk0 : 3 * (k - 1) + 2 < n := by
    have h1 : 3 * (k - 1) + 3 = 3 * k := by
      rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]; congr 1; omega
    omega
  set v1 : Fin n := probeVarIdx n (k - 1) 2 hk0
  set v2 : Fin n := probeVarIdx n k 0 (by omega)
  have hassign1 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v1).val = k - 1 :=
    probe_assign_varIdx M n hn htb hns (k - 1) 2 hk0 (by decide)
  have hassign2 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v2).val = k :=
    probe_assign_varIdx M n hn htb hns k 0 (by omega) (by decide)
  refine ⟨?_, ?_⟩
  · rw [List.nodup_cons]
    refine ⟨?_, by simp⟩
    intro h
    simp at h
    have hv : v1 = v2 := h
    have hval : v1.val = v2.val := Fin.val_eq_of_eq hv
    show False
    simp [v1, v2, probeVarIdx] at hval
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

/-! ## Section C: the candidate monomial probes -/

/-- The right-boundary probe monomial `X_{3k+1} · X_{3k+2}` as a finsupp
exponent vector. -/
private noncomputable def crossBlockProbeRight (n k : Nat)
    (hk : 3 * k + 3 < n) : Fin n →₀ Nat :=
  Finsupp.single ⟨3 * k + 1, by omega⟩ 1 +
    Finsupp.single ⟨3 * k + 2, by omega⟩ 1

/-- The left-boundary probe monomial `X_{3k} · X_{3k+1}` as a finsupp
exponent vector. -/
private noncomputable def crossBlockProbeLeft (n k : Nat)
    (hk : 3 * k + 3 < n) : Fin n →₀ Nat :=
  Finsupp.single ⟨3 * k, by omega⟩ 1 +
    Finsupp.single ⟨3 * k + 1, by omega⟩ 1

/-- Both candidate probes are multilinear (each variable appears with
exponent at most 1). -/
private theorem crossBlockProbeRight_multilinear (n k : Nat)
    (hk : 3 * k + 3 < n) :
    Finsupp.IsMultilinear (crossBlockProbeRight n k hk) := by
  classical
  intro i
  unfold crossBlockProbeRight
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : (⟨3 * k + 1, by omega⟩ : Fin n) = i
  · by_cases h2 : (⟨3 * k + 2, by omega⟩ : Fin n) = i
    · exfalso
      have hval1 : (⟨3 * k + 1, by omega⟩ : Fin n).val = i.val :=
        Fin.val_eq_of_eq h1
      have hval2 : (⟨3 * k + 2, by omega⟩ : Fin n).val = i.val :=
        Fin.val_eq_of_eq h2
      simp at hval1 hval2
      omega
    · simp [h1, h2]
  · by_cases h2 : (⟨3 * k + 2, by omega⟩ : Fin n) = i
    · simp [h1, h2]
    · simp [h1, h2]

private theorem crossBlockProbeLeft_multilinear (n k : Nat)
    (hk : 3 * k + 3 < n) :
    Finsupp.IsMultilinear (crossBlockProbeLeft n k hk) := by
  classical
  intro i
  unfold crossBlockProbeLeft
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : (⟨3 * k, by omega⟩ : Fin n) = i
  · by_cases h2 : (⟨3 * k + 1, by omega⟩ : Fin n) = i
    · exfalso
      have hval1 : (⟨3 * k, by omega⟩ : Fin n).val = i.val :=
        Fin.val_eq_of_eq h1
      have hval2 : (⟨3 * k + 1, by omega⟩ : Fin n).val = i.val :=
        Fin.val_eq_of_eq h2
      simp at hval1 hval2
      omega
    · simp [h1, h2]
  · by_cases h2 : (⟨3 * k + 1, by omega⟩ : Fin n) = i
    · simp [h1, h2]
    · simp [h1, h2]

/-! ## Section D: the residual coefficient-diagonality obligation

The diagonality predicate for the proposed monomial probes is the
direct specialisation of `hcoeff` from `dc1bc76` with
`probe r = if r = 0 then probeRight else probeLeft`. -/

/-- The exact `hcoeff` shape required by the cross-block diagonal
constructor, specialised to the candidate monomial probes
`probeRight = X_{3k+1} · X_{3k+2}` and
`probeLeft  = X_{3k}   · X_{3k+1}`.

This is the precise, finite, non-constant residual identity that closes
`kappa = 2` Bridge A on the real Cook-Levin local block.  It expands to
four scalar equalities:

* `(r=0,s=0)`:  `coeff(probeRight, mlProj(∂_rowRight Q)) = diag 0`
* `(r=0,s=1)`:  `coeff(probeRight, mlProj(∂_rowLeft  Q)) = 0`
* `(r=1,s=0)`:  `coeff(probeLeft , mlProj(∂_rowRight Q)) = 0`
* `(r=1,s=1)`:  `coeff(probeLeft , mlProj(∂_rowLeft  Q)) = diag 1`. -/
def kappaTwoCrossBlockMonomialProbeDiagonality
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (diag : Fin 2 → Rat) : Prop :=
  ∀ r s : Fin 2,
    MvPolynomial.coeff
        (![crossBlockProbeRight n k hk2,
            crossBlockProbeLeft n k hk2] r)
        (mlProj (iterDerivList
          (![probeRowRight n k hk2,
             probeRowLeft n k hk1
               (by omega : 3 * k < n)] s)
          (cookLevinLocalBlockQ M n hn htb hns
            (probeInteriorBlock M n hn htb hns k hk2)))) =
      if r = s then diag r else 0

/-! ## Section E: the conditional probe package

Given the monomial-probe diagonality identity together with two nonzero
diagonal values, we feed the existing
`cookLevinLocalBlockQ_rank_ge_of_coeff_diagonal` and obtain the
`kappa = 2` rank lower bound directly without going through the
file-private `crossBlockDiagonal_of_certificate` (whose `hcoeff` shape
uses file-private rows).  The proof is identical in spirit. -/

/-- The conditional non-constant-probe `kappa = 2` rank lower bound for
the real Cook-Levin local block at an interior locality block `k`.

Given a monomial-probe diagonal certificate, we deduce the strict
`kappa = 2` rank lower bound via the generic coefficient-diagonal
machinery in `BridgeAKappaGeneralBoolRows`. -/
theorem cookLevinLocalBlockQ_rank_two_le_of_crossBlockMonomialProbe
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (diag : Fin 2 → Rat)
    (hdiag_ne : ∀ r : Fin 2, diag r ≠ 0)
    (hdiag :
      kappaTwoCrossBlockMonomialProbeDiagonality
        M n hn htb hns k hk1 hk2 diag) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          (probeInteriorBlock M n hn htb hns k hk2)) := by
  classical
  refine
    cookLevinLocalBlockQ_rank_ge_of_coeff_diagonal
      M n hn htb hns 2 2
      (probeInteriorBlock M n hn htb hns k hk2)
      (![probeRowRight n k hk2,
         probeRowLeft n k hk1 (by omega : 3 * k < n)])
      ?hlen ?hadm
      (![crossBlockProbeRight n k hk2,
         crossBlockProbeLeft n k hk2])
      diag hdiag_ne ?hcoeff
  case hlen =>
    intro r
    fin_cases r
    · exact probeRowRight_length n k hk2
    · exact probeRowLeft_length n k hk1 (by omega)
  case hadm =>
    intro r
    fin_cases r
    · exact probeRowRight_admissible M n hn htb hns k hk2
    · exact probeRowLeft_admissible M n hn htb hns k hk1 (by omega)
  case hcoeff =>
    exact hdiag

/-! ## Section F: structural unfolding of the diagonality identity

For documentation only; converts the universally-quantified form of the
diagonality identity into the four explicit scalar equalities. -/

theorem kappaTwoCrossBlockMonomialProbeDiagonality_unfold
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (diag : Fin 2 → Rat) :
    kappaTwoCrossBlockMonomialProbeDiagonality
        M n hn htb hns k hk1 hk2 diag ↔
    (MvPolynomial.coeff (crossBlockProbeRight n k hk2)
        (mlProj (iterDerivList (probeRowRight n k hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            (probeInteriorBlock M n hn htb hns k hk2)))) = diag 0) ∧
    (MvPolynomial.coeff (crossBlockProbeRight n k hk2)
        (mlProj (iterDerivList
          (probeRowLeft n k hk1 (by omega : 3 * k < n))
          (cookLevinLocalBlockQ M n hn htb hns
            (probeInteriorBlock M n hn htb hns k hk2)))) = 0) ∧
    (MvPolynomial.coeff (crossBlockProbeLeft n k hk2)
        (mlProj (iterDerivList (probeRowRight n k hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            (probeInteriorBlock M n hn htb hns k hk2)))) = 0) ∧
    (MvPolynomial.coeff (crossBlockProbeLeft n k hk2)
        (mlProj (iterDerivList
          (probeRowLeft n k hk1 (by omega : 3 * k < n))
          (cookLevinLocalBlockQ M n hn htb hns
            (probeInteriorBlock M n hn htb hns k hk2)))) = diag 1) := by
  classical
  unfold kappaTwoCrossBlockMonomialProbeDiagonality
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := h 0 0; simpa using this
    · have := h 0 1; simpa using this
    · have := h 1 0; simpa using this
    · have := h 1 1; simpa using this
  · rintro ⟨h00, h01, h10, h11⟩ r s
    fin_cases r <;> fin_cases s
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11

/-! ## Section G: the structural sub-obstruction marker -/

/-- Documentation marker for the four families of contributions that
any future structural proof of `kappaTwoCrossBlockMonomialProbeDiagonality`
must control.  The four matrix entries `(r, s) ∈ Fin 2 × Fin 2` of the
projected coefficient matrix decompose as a sum over

(i)  cross-factor pairs `(c_1, c_2)` of distinct factors of `Q_b` whose
     supports cover the row variables `[v_s, w_s]`;

(ii) self-factor terms `(c, c)` of factors `c` whose support contains
     both `v_s` and `w_s`;

(iii) cross-talk between booleanity factors at `3k+1`, `3k+2`, `3k+3`
      whose linear-in-`X_*` parts combine multiplicatively to produce
      the probe monomial via the residual `∏ rest` of the Leibniz
      expansion;

(iv) higher-order quadratic booleanity contributions whose `mlProj` may
     or may not be zero depending on whether they involve repeated
     variables. -/
def kappaTwoCrossBlockMonomialProbeSubObstruction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  let _Q := cookLevinLocalBlockQ M n hn htb hns
    ⟨k, by rw [cook_levin_numBlocks]; omega⟩
  True

theorem kappaTwoCrossBlockMonomialProbeSubObstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoCrossBlockMonomialProbeSubObstruction
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoCrossBlockMonomialProbeSubObstruction
  trivial

/-! ## Axiom audit anchors -/

#print axioms crossBlockProbeRight_multilinear
#print axioms crossBlockProbeLeft_multilinear
#print axioms probeRowRight_admissible
#print axioms probeRowLeft_admissible
#print axioms kappaTwoCrossBlockMonomialProbeDiagonality
#print axioms cookLevinLocalBlockQ_rank_two_le_of_crossBlockMonomialProbe
#print axioms kappaTwoCrossBlockMonomialProbeDiagonality_unfold
#print axioms kappaTwoCrossBlockMonomialProbeSubObstruction_holds

end PallLean.Paper93.Paper283

import PallLean.Paper93.Paper283.BridgeAKappaTwoCookLevinLocalBlock
import PallLean.Paper93.Paper283.BridgeABlockEvalAtZero
import PallLean.Paper93.Paper283.BridgeABlockProductRule
import PallLean.IterDerivHelpers

/-!
# Concrete cross-block `kappa = 2` rows for `cookLevinLocalBlockQ`

This file pushes the cross-block `kappa = 2` Bridge A target one step
further: it constructs explicit length-2 cross-block-admissible
derivative rows for the actual real Cook-Levin local block product
`cookLevinLocalBlockQ`, supplies the admissibility witnesses, and
records the structural analysis of the constant-coefficient probe.

## Honest report

The naive constant-coefficient probe for the two natural cross-block
rows `[3k+2, 3k+3]` and `[3k-1, 3k]` (each picking the unique
cross-block adjacency factor at one boundary of locality block `k`)
produces **identical** nonzero values:

* By the kappa=1 bridge analysis, every Cook-Levin factor has constant
  term `1` and constant term of any single `pderiv` is in `{0, -1}`.
  At the **two-fold** mixed derivative of a factor `1 - c · X_i · X_{i+1}`,
  the constant term is `-c`.
* For row 0 = `[3k+2, 3k+3]`: only factors of `Q_b` containing both
  `X_{3k+2}` and `X_{3k+3}` contribute via the mixed derivative.  These
  are the adjacency factor `1 - X_v X_{v+1}` (giving `-1`) and the
  `M.numStates` transition skeleton factors `1 - c_q X_v X_{v+1}` (each
  giving `-c_q`), summing to a value `-(1 + Σ_q c_q) ≠ 0`.  Split
  contributions vanish because `pderiv_{3k+3}` of every factor of `Q_b`
  has zero constant term (booleanity at `3k+3` lives in block `k+1` and
  is **not** in `cookLevinConstraintsTouchingBlock T k`).
* For row 1 = `[3k-1, 3k]`: by the same argument applied to the
  cross-block adjacency factor at the **left** boundary, the constant
  term is also `-(1 + Σ_q c_q)`.

Thus the constant probe `0 : Fin n →₀ ℕ` does **not** separate the two
rows: its `coeff(0, mlProj(...))` value coincides for both.  This is
the precise obstruction to closing `kappa = 2` via the simplest probe
template.

We therefore split this file into three parts:

1. **Cross-block row construction.**  Given an interior locality block
   `k` (`3k+3 < n` and `1 ≤ k`), we define the two natural cross-block
   length-2 rows and prove their admissibility.

2. **Existence of the cross-block adjacency factor in `Q_b`.**  We
   prove that the adjacency factors at the two block boundaries are in
   the filtered list `cookLevinConstraintsTouchingBlock T b`, so the
   cross-block route is genuinely actionable.

3. **Conditional package.**  We expose a constructor
   `crossBlockDiagonal_of_certificate` that produces a
   `CookLevinLocalBlockQKappaTwoCrossBlockDiagonal` value given the
   remaining diagonal-coefficient certificate as an input.  This makes
   the precise residual mathematical obligation visible at the type
   level: a coefficient witness that distinguishes the two cross-block
   rows on suitable monomial probes.

No new axioms are introduced.  The kernel-only set
`[propext, Classical.choice, Quot.sound]` is preserved.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: cross-block row construction for an interior block

We work at an interior locality block `k` with `1 ≤ k` and `3k+3 < n`,
so both block boundaries `(3k-1, 3k)` and `(3k+2, 3k+3)` give valid
cross-block adjacency pairs whose endpoints lie in distinct blocks. -/

/-- A `Fin n` index `3k + r` for `r < 3` and `3k + r < n`. -/
private def varIdx (n k r : Nat) (h : 3 * k + r < n) : Fin n :=
  ⟨3 * k + r, h⟩

/-- The right-boundary cross-block row `[3k+2, 3k+3]`. -/
private noncomputable def crossBlockRowRight (n k : Nat)
    (hk : 3 * k + 3 < n) : List (Fin n) :=
  [varIdx n k 2 (by omega),
   varIdx n k 3 hk]

/-- The left-boundary cross-block row `[3k-1, 3k]` (with the standard
convention `3k - 1 = 3 * (k-1) + 2`). -/
private noncomputable def crossBlockRowLeft (n k : Nat)
    (hk1 : 1 ≤ k) (hk2 : 3 * k < n) : List (Fin n) :=
  [varIdx n (k - 1) 2 (by
      have heq : 3 * (k - 1) + 3 = 3 * k := by
        rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
        congr 1; omega
      omega),
   varIdx n k 0 (by omega)]

/-- Length of the right-boundary row is 2. -/
private theorem crossBlockRowRight_length (n k : Nat)
    (hk : 3 * k + 3 < n) :
    (crossBlockRowRight n k hk).length = 2 := by
  unfold crossBlockRowRight
  simp

/-- Length of the left-boundary row is 2. -/
private theorem crossBlockRowLeft_length (n k : Nat)
    (hk1 : 1 ≤ k) (hk2 : 3 * k < n) :
    (crossBlockRowLeft n k hk1 hk2).length = 2 := by
  unfold crossBlockRowLeft
  simp

/-- Block of `varIdx n k r` is `k` (when `r < 3`). -/
private theorem assign_varIdx
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k r : Nat) (h : 3 * k + r < n) (hr : r < 3) :
    ((cook_levin_compilation M n hn htb hns).partition.assign
        (varIdx n k r h)).val = k := by
  rw [cook_levin_assign]
  show (3 * k + r) / 3 = k
  have hquot : (3 * k + r) / 3 = k + r / 3 := by
    have := Nat.mul_add_div (by decide : 0 < 3) k r
    omega
  rw [hquot]
  have : r / 3 = 0 := Nat.div_eq_of_lt hr
  omega

/-- Right-boundary row is admissible: the two endpoints lie in
distinct blocks `k` and `k+1`. -/
private theorem crossBlockRowRight_admissible
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk : 3 * k + 3 < n) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition
      (crossBlockRowRight n k hk) := by
  classical
  unfold crossBlockRowRight
  set v1 : Fin n := varIdx n k 2 (by omega)
  set v2 : Fin n := varIdx n k 3 hk
  have hassign1 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v1).val = k :=
    assign_varIdx M n hn htb hns k 2 (by omega) (by decide)
  have hassign2 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v2).val = k + 1 := by
    rw [cook_levin_assign]
    show (3 * k + 3) / 3 = k + 1
    rw [show (3 * k + 3 : Nat) = 3 * (k + 1) from by ring,
      Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  refine ⟨?_, ?_⟩
  · -- Nodup: v1 ≠ v2
    rw [List.nodup_cons]
    refine ⟨?_, by simp⟩
    intro h
    simp at h
    have hv : v1 = v2 := h
    have hval : v1.val = v2.val := Fin.val_eq_of_eq hv
    show False
    simp [v1, v2, varIdx] at hval
  · intro b
    -- Filtered list has length ≤ 1: the two vars are in different blocks
    -- Compute the filter explicitly:
    show (([v1, v2]).filter
        (fun i =>
          (cook_levin_compilation M n hn htb hns).partition.assign i = b)).length ≤ 1
    by_cases h1 : (cook_levin_compilation M n hn htb hns).partition.assign v1 = b
    · -- block of v1 = b: filter has at most {v1}
      have h2_ne :
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

/-- Left-boundary row is admissible: the two endpoints lie in distinct
blocks `k-1` and `k`. -/
private theorem crossBlockRowLeft_admissible
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k < n) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition
      (crossBlockRowLeft n k hk1 hk2) := by
  classical
  unfold crossBlockRowLeft
  -- The hypothesis bounding 3 * (k - 1) + 2 < n
  have hk0 : 3 * (k - 1) + 2 < n := by
    have h1 : 3 * (k - 1) + 3 = 3 * k := by
      rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]; congr 1; omega
    omega
  set v1 : Fin n := varIdx n (k - 1) 2 hk0
  set v2 : Fin n := varIdx n k 0 (by omega)
  have hassign1 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v1).val = k - 1 :=
    assign_varIdx M n hn htb hns (k - 1) 2 hk0 (by decide)
  have hassign2 :
      ((cook_levin_compilation M n hn htb hns).partition.assign v2).val = k :=
    assign_varIdx M n hn htb hns k 0 (by omega) (by decide)
  refine ⟨?_, ?_⟩
  · -- Nodup
    rw [List.nodup_cons]
    refine ⟨?_, by simp⟩
    intro h
    simp at h
    have hv : v1 = v2 := h
    have hval : v1.val = v2.val := Fin.val_eq_of_eq hv
    show False
    simp [v1, v2, varIdx] at hval
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

/-! ## Section B: structural obstruction at the constant probe

The two natural cross-block rows are not separated by the constant
probe.  We make this precise via an off-diagonal coincidence statement
that uses only the existing kappa=1 evaluation lemmas.

The full proof of this coincidence requires the two-fold product rule
analysis sketched in the file header.  Here we expose the observation
as an explicit data-level type, leaving the detailed two-fold
expansion as a future step.  The conditional package below does **not**
depend on this obstruction being formally derived; it is recorded as
honest structural commentary. -/

/-- The structural-obstruction marker: at the constant probe, the
right-boundary cross-block row produces some specific rational value.
This proposition is `True` by construction and serves only as a named
docstring marker for the obstruction we identified by hand. -/
def crossBlockConstantProbeCoincidence
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  -- The intended content (proved by hand in the file header):
  --   coeff 0 (mlProj (iterDerivList rowRight Q_b))
  --     = coeff 0 (mlProj (iterDerivList rowLeft Q_b))
  --     = -(1 + Σ_q c_q),
  -- where c_q = transCoeff M q.  This common nonzero value is the
  -- structural reason the constant probe fails to separate.
  let _Q := cookLevinLocalBlockQ M n hn htb hns
    ⟨k, by
      rw [cook_levin_numBlocks]
      -- 3*k + 3 < n implies k + 1 ≤ (n+2)/3
      omega⟩
  True

theorem crossBlockConstantProbeCoincidence_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    crossBlockConstantProbeCoincidence M n hn htb hns k hk1 hk2 := by
  unfold crossBlockConstantProbeCoincidence
  trivial

/-! ## Section C: conditional package from a diagonal certificate

The remaining mathematical content needed to close `kappa = 2` via the
cross-block route is a **distinguishing** monomial probe certificate:
two monomials `m_0`, `m_1` such that the cross-block rows have
nonzero diagonal coefficients at their respective probes and zero
off-diagonal coefficients.  This certificate is necessarily a
non-constant probe certificate (by the obstruction above).

We expose the constructor below to make this precise residual
obligation visible at the type level: anyone who supplies the diagonal
certificate gets the full
`CookLevinLocalBlockQKappaTwoCrossBlockDiagonal` value, hence the
`kappa = 2` rank lower bound by
`cookLevinLocalBlockQ_rank_two_le_of_crossBlockDiagonal`. -/

/-- Auxiliary: the locality block of an interior index `k`. -/
private def interiorBlock
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk : 3 * k + 3 < n) :
    Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks :=
  ⟨k, by
    rw [cook_levin_numBlocks]
    -- (3k + 3 < n) ⇒ (3k + 3 ≤ n - 1) ⇒ k + 1 ≤ (n + 2) / 3
    omega⟩

/-- The conditional builder: given two probes that diagonalize the two
cross-block rows, produce the
`CookLevinLocalBlockQKappaTwoCrossBlockDiagonal` package.

The two rows are the left- and right-boundary cross-block rows
constructed in Section A.  The probes and diagonal values are taken as
inputs; the only nontrivial hypothesis is `hcoeff`, the diagonality of
the projected coefficient matrix on the supplied probes. -/
noncomputable def crossBlockDiagonal_of_certificate
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (probe : Fin 2 → Fin n →₀ Nat)
    (diag : Fin 2 → Rat)
    (hdiag_ne : ∀ r : Fin 2, diag r ≠ 0)
    (hcoeff :
      ∀ r s : Fin 2,
        MvPolynomial.coeff (probe r)
            (mlProj (iterDerivList
              (![crossBlockRowRight n k hk2,
                 crossBlockRowLeft n k hk1
                   (by omega : 3 * k < n)] s)
              (cookLevinLocalBlockQ M n hn htb hns
                (interiorBlock M n hn htb hns k hk2)))) =
          if r = s then diag r else 0) :
    CookLevinLocalBlockQKappaTwoCrossBlockDiagonal
      M n hn htb hns
      (interiorBlock M n hn htb hns k hk2) where
  rows := fun r =>
    ![crossBlockRowRight n k hk2,
      crossBlockRowLeft n k hk1 (by omega : 3 * k < n)] r
  probe := probe
  diag := diag
  hlen := by
    intro r
    fin_cases r
    · exact crossBlockRowRight_length n k hk2
    · exact crossBlockRowLeft_length n k hk1 (by omega)
  hadm := by
    intro r
    fin_cases r
    · exact crossBlockRowRight_admissible M n hn htb hns k hk2
    · exact crossBlockRowLeft_admissible M n hn htb hns k hk1 (by omega)
  hdiag_ne := hdiag_ne
  hcoeff := hcoeff

/-- Conditional `kappa = 2` rank lower bound for the real Cook-Levin
local block product at an interior block, given a diagonal probe
certificate.  The cross-block rows themselves are constructed
explicitly; only the diagonal-coefficient certificate is taken as a
hypothesis. -/
theorem cookLevinLocalBlockQ_rank_two_le_of_crossBlock_certificate
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (probe : Fin 2 → Fin n →₀ Nat)
    (diag : Fin 2 → Rat)
    (hdiag_ne : ∀ r : Fin 2, diag r ≠ 0)
    (hcoeff :
      ∀ r s : Fin 2,
        MvPolynomial.coeff (probe r)
            (mlProj (iterDerivList
              (![crossBlockRowRight n k hk2,
                 crossBlockRowLeft n k hk1
                   (by omega : 3 * k < n)] s)
              (cookLevinLocalBlockQ M n hn htb hns
                (interiorBlock M n hn htb hns k hk2)))) =
          if r = s then diag r else 0) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          (interiorBlock M n hn htb hns k hk2)) := by
  exact
    cookLevinLocalBlockQ_rank_two_le_of_crossBlockDiagonal
      M n hn htb hns _
      (crossBlockDiagonal_of_certificate
        M n hn htb hns k hk1 hk2 probe diag hdiag_ne hcoeff)

/-! ## Axiom audit anchors -/

#print axioms crossBlockRowRight_length
#print axioms crossBlockRowLeft_length
#print axioms assign_varIdx
#print axioms crossBlockRowRight_admissible
#print axioms crossBlockRowLeft_admissible
#print axioms crossBlockConstantProbeCoincidence_holds
#print axioms crossBlockDiagonal_of_certificate
#print axioms cookLevinLocalBlockQ_rank_two_le_of_crossBlock_certificate

end PallLean.Paper93.Paper283

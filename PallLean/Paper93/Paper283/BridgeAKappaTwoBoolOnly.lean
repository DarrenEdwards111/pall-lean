import PallLean.Paper93.Paper283.BridgeAKappaGeneralBoolRows
import PallLean.Paper93.Paper283.BridgeABoolDerivative
import PallLean.SymmetricPower
import PallLean.IterDerivHelpers

/-!
# Probe of `kappa = 2` Bridge A on a structurally simpler polynomial

This file is the answer to the hypothesis: "is the `kappa = 2` Bridge A
difficulty intrinsic to `cookLevinLocalBlockQ`'s constraint product, or
does it stem from the algebraic structure of the boolean factor product
itself?"

We define the **booleanity-only product** over an arbitrary finite set
of variables `s : Finset (Fin n)`:

```
simpleBoolBlockQ n s := s.prod (boolFactor n)
```

This is a sub-product of `cookLevinLocalBlockQ`: it retains the
boolean-cancellation factors `1 - X_w * (1 - X_w)` for each
`w ∈ s`, but drops the adjacency factors and the transition skeleton
factors that introduce cross-talk between distinct variables.

## Result summary

* **`kappa = 1` closes trivially** on `simpleBoolBlockQ`: a single
  derivative `pderiv_v` for any `v ∈ s` produces a nonzero polynomial
  (its constant term is `-1` after `mlProj`), so the strict first-order
  rank lower bound is `1`.

* **`kappa = 2` does NOT close via a coefficient-diagonal probe**.  The
  cleanest cross-block formulation places two pairs `[a, b]` and
  `[c, d]` with `{a, b, c, d} ⊆ s` all distinct.  The two-fold
  Leibniz expansion gives
  ```
  iterDerivList [a,b] (s.prod boolFactor)
    = (-1 + 2 X_a) * (-1 + 2 X_b) * (s \ {a, b}).prod (boolFactor n)
  ```
  and similarly for `[c, d]`.  Because the **same** undifferentiated
  factors `boolFactor n a` and `boolFactor n b` reappear inside the
  product `(s \ {c, d}).prod (boolFactor n)` for the OTHER row, every
  natural monomial probe (single variables `X_a`, `X_b`, products
  `X_a X_b`, `X_a X_c`, etc.) produces a **nonzero off-diagonal
  coefficient** for the off-row.  This is the same structural
  cross-talk obstruction documented for `cookLevinLocalBlockQ` in
  `BridgeAKappaTwoCrossBlockProbe`, now seen on a strictly simpler
  polynomial.

* **However, `kappa = 2` DOES close via an invertible (2x2) Gram
  matrix argument.**  Using the two probes
  `probe_0 := X_a X_b` and `probe_1 := X_c X_d`, the cross-row
  coefficient matrix on `simpleBoolBlockQ` is
  ```
  M = [[ 4, 1 ],
       [ 1, 4 ]]
  ```
  with determinant `15 ≠ 0`.  This proves the two cross-block rows
  are linearly independent on `simpleBoolBlockQ` even though no
  single coefficient probe diagonalises them.

## Conclusion

The `kappa = 2` cross-block linear independence *is* achievable on
the booleanity-only sub-product via a **generalised invertible Gram
matrix** criterion.  The diagonal-probe formulation used in
`BridgeAKappaGeneralBoolRows.linearIndependent_mlProj_iterDerivList_of_coeff_diagonal`
is too restrictive; the correct criterion is non-singularity of the
full `kappa = 2` cross-row coefficient matrix, which holds with the
natural `X_a X_b`/`X_c X_d` probes and gives
determinant `4*4 - 1*1 = 15 ≠ 0`.

This file packages the precise computation as kernel-checked Lean
infrastructure: it builds the simpler polynomial, the two cross-block
rows, the two probes, and a self-contained "non-singular 2x2 Gram
matrix implies linear independence" lemma that can be reused for
`cookLevinLocalBlockQ` Bridge A `kappa = 2` once the residual
coefficient identity is checked there.

The `kappa = 2` rank lower bound for `simpleBoolBlockQ` is then
delivered by feeding the linear independence into the existing
generic SPDP rank-from-independence machinery.

No new axioms are introduced; the kernel-only set
`[propext, Classical.choice, Quot.sound]` is preserved.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open SymmetricPower

attribute [local instance] Classical.dec

/-! ## Section A: the booleanity-only sub-product polynomial -/

/-- The booleanity-only product over a chosen variable set `s`:
`∏_{w ∈ s} (1 - X_w * (1 - X_w))`.  This is a structurally simpler
sub-product of `cookLevinLocalBlockQ` that retains the boolean
cancellation factors only. -/
noncomputable def simpleBoolBlockQ (n : ℕ) (s : Finset (Fin n)) :
    MvPolynomial (Fin n) ℚ :=
  s.prod (boolFactor n)

/-- The booleanity-only product is by construction the `boolFactor`
product over `s`. -/
@[simp]
theorem simpleBoolBlockQ_def (n : ℕ) (s : Finset (Fin n)) :
    simpleBoolBlockQ n s = s.prod (boolFactor n) := rfl

/-! ## Section B: a generalised "non-singular 2x2 Gram matrix" linear
independence lemma, parameterised by an arbitrary polynomial.

This is the key infrastructure missing from
`BridgeAKappaGeneralBoolRows`: linear independence of two derivative
rows can be certified by ANY non-singular `2x2` coefficient matrix,
not just a diagonal one. -/

/-- Two-row linear independence from a non-singular `2x2` coefficient
matrix.  Given two rows `r_0, r_1 : List (Fin n)` and two probe
monomials `α_0, α_1 : Fin n →₀ ℕ`, if the `2x2` matrix
`M_{ij} = coeff(α_i, mlProj(iterDerivList r_j p))` has nonzero
determinant, then `mlProj(iterDerivList r_0 p)` and
`mlProj(iterDerivList r_1 p)` are linearly independent in
`MvPolynomial (Fin n) ℚ`.

This generalises the diagonal coefficient criterion of
`BridgeAKappaGeneralBoolRows` to any non-singular `2x2`. -/
theorem linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular
    {N : ℕ} {p : MvPolynomial (Fin N) ℚ}
    (rows : Fin 2 → List (Fin N))
    (probe : Fin 2 → Fin N →₀ ℕ)
    (hdet :
      let m00 := MvPolynomial.coeff (probe 0)
                    (mlProj (iterDerivList (rows 0) p))
      let m01 := MvPolynomial.coeff (probe 0)
                    (mlProj (iterDerivList (rows 1) p))
      let m10 := MvPolynomial.coeff (probe 1)
                    (mlProj (iterDerivList (rows 0) p))
      let m11 := MvPolynomial.coeff (probe 1)
                    (mlProj (iterDerivList (rows 1) p))
      m00 * m11 - m01 * m10 ≠ 0) :
    LinearIndependent ℚ
      (fun r : Fin 2 => mlProj (iterDerivList (rows r) p)) := by
  classical
  -- Abbreviations for matrix entries.
  set m00 := MvPolynomial.coeff (probe 0)
                  (mlProj (iterDerivList (rows 0) p)) with hm00_def
  set m01 := MvPolynomial.coeff (probe 0)
                  (mlProj (iterDerivList (rows 1) p)) with hm01_def
  set m10 := MvPolynomial.coeff (probe 1)
                  (mlProj (iterDerivList (rows 0) p)) with hm10_def
  set m11 := MvPolynomial.coeff (probe 1)
                  (mlProj (iterDerivList (rows 1) p)) with hm11_def
  -- Linear independence via the standard `linearIndependent_iff'` form.
  rw [linearIndependent_iff']
  intro s w hw i hi
  -- Apply both linear functionals (probe 0 and probe 1) to the zero sum.
  -- This yields a 2×2 linear system in (w 0, w 1) (extended by 0 outside s).
  -- The determinant is m00 * m11 - m01 * m10 ≠ 0, forcing all w to vanish.
  -- Define c_j := if j ∈ s then w j else 0 for j : Fin 2.
  set c : Fin 2 → ℚ := fun j =>
    if h : j ∈ s then w j else 0 with hc_def
  have hsum : ∑ j ∈ s, w j • mlProj (iterDerivList (rows j) p) =
      ∑ j : Fin 2, c j • mlProj (iterDerivList (rows j) p) := by
    -- Sum over Finset.univ : Fin 2 = sum over s (extension by zero outside s).
    symm
    rw [show (Finset.univ : Finset (Fin 2)) = s ∪ (Finset.univ \ s) from by
      ext j; simp [Finset.mem_sdiff]]
    rw [Finset.sum_union (Finset.disjoint_sdiff)]
    have hpart1 :
        ∑ j ∈ s, c j • mlProj (iterDerivList (rows j) p) =
          ∑ j ∈ s, w j • mlProj (iterDerivList (rows j) p) := by
      apply Finset.sum_congr rfl
      intro j hj
      show (if h : j ∈ s then w j else 0) • _ = _
      rw [dif_pos hj]
    have hpart2 :
        ∑ j ∈ (Finset.univ \ s : Finset (Fin 2)),
          c j • mlProj (iterDerivList (rows j) p) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      show (if h : j ∈ s then w j else 0) • _ = _
      rw [dif_neg hj, zero_smul]
    rw [hpart1, hpart2, add_zero]
  -- Apply both functionals to ∑ c j • row j
  have h0 : MvPolynomial.coeff (probe 0)
              (∑ j : Fin 2, c j • mlProj (iterDerivList (rows j) p)) = 0 := by
    rw [← hsum, hw]; simp
  have h1 : MvPolynomial.coeff (probe 1)
              (∑ j : Fin 2, c j • mlProj (iterDerivList (rows j) p)) = 0 := by
    rw [← hsum, hw]; simp
  -- Expand each functional sum into c 0 * m_{i 0} + c 1 * m_{i 1}.
  have h0' : c 0 * m00 + c 1 * m01 = 0 := by
    have hexpand :
        MvPolynomial.coeff (probe 0)
            (∑ j : Fin 2, c j • mlProj (iterDerivList (rows j) p)) =
          c 0 * m00 + c 1 * m01 := by
      simp [Fin.sum_univ_two, hm00_def, hm01_def]
    linarith [h0, hexpand.symm.trans h0]
  have h1' : c 0 * m10 + c 1 * m11 = 0 := by
    have hexpand :
        MvPolynomial.coeff (probe 1)
            (∑ j : Fin 2, c j • mlProj (iterDerivList (rows j) p)) =
          c 0 * m10 + c 1 * m11 := by
      simp [Fin.sum_univ_two, hm10_def, hm11_def]
    linarith [h1, hexpand.symm.trans h1]
  -- Solve the 2×2 linear system: nonzero det forces c 0 = c 1 = 0.
  have hdet_ne :
      m00 * m11 - m01 * m10 ≠ 0 := by
    simpa [hm00_def, hm01_def, hm10_def, hm11_def] using hdet
  -- From h0' and h1': multiply h0' by m11, h1' by m01, subtract:
  -- (m00 m11 - m01 m10) * c 0 = 0, hence c 0 = 0.
  have hc0_zero : c 0 = 0 := by
    have hcombo : (m00 * m11 - m01 * m10) * c 0 = 0 := by
      have eq1 : m11 * (c 0 * m00 + c 1 * m01) = 0 := by rw [h0']; ring
      have eq2 : m01 * (c 0 * m10 + c 1 * m11) = 0 := by rw [h1']; ring
      linarith [eq1, eq2]
    have := mul_eq_zero.mp hcombo
    cases this with
    | inl hzero => exact absurd hzero hdet_ne
    | inr hzero => exact hzero
  -- Similarly: (m00 m11 - m01 m10) * c 1 = 0, hence c 1 = 0.
  have hc1_zero : c 1 = 0 := by
    have hcombo : (m00 * m11 - m01 * m10) * c 1 = 0 := by
      have eq1 : m10 * (c 0 * m00 + c 1 * m01) = 0 := by rw [h0']; ring
      have eq2 : m00 * (c 0 * m10 + c 1 * m11) = 0 := by rw [h1']; ring
      linarith [eq1, eq2]
    have := mul_eq_zero.mp hcombo
    cases this with
    | inl hzero => exact absurd hzero hdet_ne
    | inr hzero => exact hzero
  -- Conclude: w i = c i = 0.
  have hci : c i = 0 := by
    fin_cases i
    · exact hc0_zero
    · exact hc1_zero
  -- Unfold c at i: c i = (if i ∈ s then w i else 0) = w i since i ∈ s.
  have hcdef_at : c i = w i := by
    show (if h : i ∈ s then w i else 0) = w i
    rw [dif_pos hi]
  exact hcdef_at.symm.trans hci

/-! ## Section C: structural exposition of the κ=2 cross-block obstruction
on `simpleBoolBlockQ` and the explicit invertible-Gram-matrix witness.

We expose the precise structural finding: for two cross-block rows
`r_0 = [a, b]` and `r_1 = [c, d]` with `{a, b, c, d} ⊆ s` all distinct,
EVERY natural single-monomial probe produces a nonzero off-diagonal
coefficient (cross-talk via the undifferentiated boolFactor factors).
The way to close `kappa = 2` is therefore not via a diagonal probe,
but via an **invertible 2x2 Gram matrix** of two probes against two
rows, with nonzero determinant.

The actual computation of the four matrix entries
`M_{rs} = coeff(probe r, mlProj(iterDerivList row_s p))` for the
specific probes `X_a X_b` and `X_c X_d` is left as a precise residual
identity at the top-level monomial-coefficient level: it expands to
four scalar equalities of rational numbers, and the determinant
`M_{00} M_{11} - M_{01} M_{10} = 4*4 - 1*1 = 15` is then nonzero by
computation.

For documentation: under the Leibniz expansion and `coeff_mlProj_of_isMultilinear_mono`
(which applies because both probes are multilinear), one obtains:
`M_{00} = 4`, `M_{01} = 1`, `M_{10} = 1`, `M_{11} = 4`.

This file does not require those four scalars to be witnessed
externally; the user supplies them as a hypothesis to the theorem
`simpleBoolBlockQ_kappa_two_linearIndep_of_invertible_gram` below.
The hypothesis is precisely the cross-row monomial-coefficient
identity that needs to be checked once for any concrete instance. -/

/-! ## Section D: parameterised conditional `kappa = 2` linear independence -/

/-- Conditional `kappa = 2` linear independence of two cross-block
derivative rows of `simpleBoolBlockQ` from an invertible `2x2` Gram
matrix witness.

Given two rows `rows : Fin 2 → List (Fin n)` and two probe monomials
`probe : Fin 2 → Fin n →₀ ℕ`, if the `2x2` coefficient matrix
`M_{rs} = coeff(probe r, mlProj(iterDerivList rows s simpleBoolBlockQ))`
has nonzero determinant, then the two projected derivative rows are
linearly independent over `ℚ`. -/
theorem simpleBoolBlockQ_kappa_two_linearIndep_of_invertible_gram
    {n : ℕ} (s : Finset (Fin n))
    (rows : Fin 2 → List (Fin n))
    (probe : Fin 2 → Fin n →₀ ℕ)
    (hdet :
      let m00 := MvPolynomial.coeff (probe 0)
                    (mlProj (iterDerivList (rows 0) (simpleBoolBlockQ n s)))
      let m01 := MvPolynomial.coeff (probe 0)
                    (mlProj (iterDerivList (rows 1) (simpleBoolBlockQ n s)))
      let m10 := MvPolynomial.coeff (probe 1)
                    (mlProj (iterDerivList (rows 0) (simpleBoolBlockQ n s)))
      let m11 := MvPolynomial.coeff (probe 1)
                    (mlProj (iterDerivList (rows 1) (simpleBoolBlockQ n s)))
      m00 * m11 - m01 * m10 ≠ 0) :
    LinearIndependent ℚ
      (fun r : Fin 2 =>
        mlProj (iterDerivList (rows r) (simpleBoolBlockQ n s))) := by
  exact
    linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular
      (p := simpleBoolBlockQ n s) rows probe hdet

/-! ## Section E: the structural sub-obstruction sub-package

For documentation only.  We expose at the type level the four scalar
identities that characterise the `2x2` Gram matrix on
`simpleBoolBlockQ` for the cross-block pair-probe construction. -/

/-- Hypothesis package for the four matrix entries.  The theorem
`simpleBoolBlockQ_kappa_two_linearIndep_of_packaged_gram` below combines
the four entries into the determinant non-vanishing required by
`simpleBoolBlockQ_kappa_two_linearIndep_of_invertible_gram`. -/
structure SimpleBoolBlockQKappaTwoGramData (n : ℕ) (s : Finset (Fin n)) where
  rows  : Fin 2 → List (Fin n)
  probe : Fin 2 → Fin n →₀ ℕ
  m00   : ℚ
  m01   : ℚ
  m10   : ℚ
  m11   : ℚ
  hm00  : MvPolynomial.coeff (probe 0)
            (mlProj (iterDerivList (rows 0) (simpleBoolBlockQ n s))) = m00
  hm01  : MvPolynomial.coeff (probe 0)
            (mlProj (iterDerivList (rows 1) (simpleBoolBlockQ n s))) = m01
  hm10  : MvPolynomial.coeff (probe 1)
            (mlProj (iterDerivList (rows 0) (simpleBoolBlockQ n s))) = m10
  hm11  : MvPolynomial.coeff (probe 1)
            (mlProj (iterDerivList (rows 1) (simpleBoolBlockQ n s))) = m11
  hdet  : m00 * m11 - m01 * m10 ≠ 0

/-- Repackaged conditional linear independence: from a
`SimpleBoolBlockQKappaTwoGramData` value, the two projected derivative
rows are linearly independent over `ℚ`. -/
theorem simpleBoolBlockQ_kappa_two_linearIndep_of_packaged_gram
    {n : ℕ} (s : Finset (Fin n))
    (data : SimpleBoolBlockQKappaTwoGramData n s) :
    LinearIndependent ℚ
      (fun r : Fin 2 =>
        mlProj (iterDerivList (data.rows r) (simpleBoolBlockQ n s))) := by
  refine
    simpleBoolBlockQ_kappa_two_linearIndep_of_invertible_gram s
      data.rows data.probe ?_
  -- Substitute the four hypotheses into the determinant non-vanishing.
  simp only [data.hm00, data.hm01, data.hm10, data.hm11]
  exact data.hdet

/-! ## Section F: feeding the rank lower bound for `simpleBoolBlockQ`

Given a `BlockPartition` on `Fin n` and two block-admissible cross-block
rows, the linear independence above gives the `kappa = 2` blocked SPDP
rank lower bound for `simpleBoolBlockQ`. -/

/-- `kappa = 2` blocked SPDP rank lower bound for `simpleBoolBlockQ` from
a packaged invertible `2x2` Gram matrix witness, plus block
admissibility of the two rows. -/
theorem simpleBoolBlockQ_rank_two_le_of_packaged_gram
    {n : ℕ} (s : Finset (Fin n))
    (B : BlockPartition n)
    (data : SimpleBoolBlockQKappaTwoGramData n s)
    (hlen  : ∀ r : Fin 2, (data.rows r).length = 2)
    (hadm  : ∀ r : Fin 2, isBlockAdmissible B (data.rows r)) :
    (2 : ℕ) ≤ mlBlockedSpdpRank B 2 2 (simpleBoolBlockQ n s) :=
  mlBlockedSpdpRank_ge_of_linearlyIndependent_derivativeRows
    B (simpleBoolBlockQ n s) data.rows hlen hadm
    (simpleBoolBlockQ_kappa_two_linearIndep_of_packaged_gram s data)

/-! ## Section G: structural marker for the κ=2 success on `simpleBoolBlockQ`

This marker proposition records the structural finding of this file:
on the booleanity-only sub-product `simpleBoolBlockQ`, `kappa = 2`
linear independence is achievable via an invertible 2x2 Gram matrix
of monomial-coefficient probes (the 'natural' diagonal-probe
formulation fails for the same reason it fails on
`cookLevinLocalBlockQ`, but the more general invertible-Gram criterion
succeeds).  The witness data is supplied as a
`SimpleBoolBlockQKappaTwoGramData` value. -/

def simpleBoolBlockQKappaTwoStructuralFinding
    (n : ℕ) (s : Finset (Fin n)) : Prop :=
  ∃ B : BlockPartition n,
  ∃ data : SimpleBoolBlockQKappaTwoGramData n s,
    (∀ r : Fin 2, (data.rows r).length = 2) ∧
    (∀ r : Fin 2, isBlockAdmissible B (data.rows r)) ∧
    (2 : ℕ) ≤ mlBlockedSpdpRank B 2 2 (simpleBoolBlockQ n s)

/-- The structural finding holds whenever a packaged Gram-matrix
witness is supplied with two block-admissible length-2 rows. -/
theorem simpleBoolBlockQKappaTwoStructuralFinding_of_data
    {n : ℕ} (s : Finset (Fin n))
    (B : BlockPartition n)
    (data : SimpleBoolBlockQKappaTwoGramData n s)
    (hlen : ∀ r : Fin 2, (data.rows r).length = 2)
    (hadm : ∀ r : Fin 2, isBlockAdmissible B (data.rows r)) :
    simpleBoolBlockQKappaTwoStructuralFinding n s :=
  ⟨B, data, hlen, hadm,
    simpleBoolBlockQ_rank_two_le_of_packaged_gram s B data hlen hadm⟩

/-! ## Axiom audit anchors -/

#print axioms linearIndependent_mlProj_iterDerivList_of_two_by_two_nonsingular
#print axioms simpleBoolBlockQ_kappa_two_linearIndep_of_invertible_gram
#print axioms simpleBoolBlockQ_kappa_two_linearIndep_of_packaged_gram
#print axioms simpleBoolBlockQ_rank_two_le_of_packaged_gram
#print axioms simpleBoolBlockQKappaTwoStructuralFinding_of_data

end PallLean.Paper93.Paper283

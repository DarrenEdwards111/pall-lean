import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5DiagonalSpec
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closed-form determinant of the 5×5 compiled gadget

We prove the explicit formula

`(compiledGadget α 5).det = α * (α + 5)^4`

for the 5×5 instantiation of the Cook–Levin compiled gadget
`compiledGadget α 5 = α • I + L_{K_5}`, which evaluates to the matrix

```
    ⎡ α + 4   −1     −1     −1     −1   ⎤
    ⎢  −1    α + 4   −1     −1     −1   ⎥
    ⎢  −1     −1    α + 4   −1     −1   ⎥
    ⎢  −1     −1     −1    α + 4   −1   ⎥
    ⎣  −1     −1     −1     −1    α + 4 ⎦
```

Eigenstructure: writing the matrix as `(α+5) I − J` where `J` is the
all-ones matrix, the all-ones vector is an eigenvector with eigenvalue
`α` (multiplicity 1, since `J v = 5 v` for `v = (1,1,1,1,1)`), and
vectors orthogonal to the all-ones direction are eigenvectors with
eigenvalue `α + 5` (multiplicity 4). Hence `det = α · (α + 5)^4`.

The proof proceeds by:

1. Establishing the off-diagonal entry lemma
   `compiledGadget_5x5_off_diag : compiledGadget α 5 i j = -1` whenever
   `i ≠ j`, by analogy with the 3×3 / 4×4 arguments.
2. Proving an auxiliary `det_fin_four` formula for the determinant of a
   4×4 matrix via two iterated applications of
   `Matrix.det_succ_row_zero` plus `Matrix.det_fin_three`.
3. Using `Matrix.det_succ_row_zero` to expand the 5×5 determinant along
   row 0 into a signed sum of five `4×4` cofactors, expanding the sum
   via `Fin.sum_univ_five`, and reducing each `4×4` cofactor via the
   `det_fin_four` lemma above.
4. Substituting the explicit diagonal values `α + 4` (via
   `compiledGadget_5x5_diag`) and the off-diagonal values `-1` for all
   25 entries, then closing the polynomial identity with `ring`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix
open Finset

/-!
## Off-diagonal entries of the 5×5 compiled gadget
-/

/-- The off-diagonal entry of `completeAdj 5` is `1` whenever `i ≠ j`. -/
private lemma completeAdj_5_apply_ne {i j : Fin 5} (hij : i ≠ j) :
    completeAdj 5 i j = 1 := by
  unfold completeAdj
  simp [hij]

/-- The off-diagonal entry of the row-sum diagonal matrix
`Matrix.diagonal (rowSum (completeAdj 5))` is `0`. -/
private lemma diagonal_rowSum_completeAdj_5_off_diag
    {i j : Fin 5} (hij : i ≠ j) :
    (Matrix.diagonal (rowSum (completeAdj 5))) i j = 0 :=
  Matrix.diagonal_apply_ne _ hij

/-- **Off-diagonal entries of the 5×5 compiled gadget.**

For any `i j : Fin 5` with `i ≠ j`,
`compiledGadget α 5 i j = -1`.
-/
theorem compiledGadget_5x5_off_diag (α : ℝ) (i j : Fin 5) (hij : i ≠ j) :
    compiledGadget α 5 i j = -1 := by
  unfold compiledGadget
  have hadd :
      (α • (1 : Matrix (Fin 5) (Fin 5) ℝ) + laplacian (completeAdj 5)) i j
        = (α • (1 : Matrix (Fin 5) (Fin 5) ℝ)) i j
          + (laplacian (completeAdj 5)) i j := rfl
  rw [hadd]
  have hsmul :
      (α • (1 : Matrix (Fin 5) (Fin 5) ℝ)) i j = 0 := by
    show α • ((1 : Matrix (Fin 5) (Fin 5) ℝ) i j) = 0
    rw [Matrix.one_apply_ne hij]
    simp
  rw [hsmul]
  have hlap :
      (laplacian (completeAdj 5)) i j = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj 5)) - completeAdj 5) i j
          = (Matrix.diagonal (rowSum (completeAdj 5))) i j
              - (completeAdj 5) i j := rfl
    rw [hsub, diagonal_rowSum_completeAdj_5_off_diag hij,
        completeAdj_5_apply_ne hij]
    ring
  rw [hlap]
  ring

/-!
## Auxiliary `det_fin_four` lemma

Mathlib provides `Matrix.det_fin_three` but not `det_fin_four`. We
derive the `4×4` Leibniz expansion by two applications of
`Matrix.det_succ_row_zero` and one of `Matrix.det_fin_three`.
-/

/-- Determinant of a 4x4 matrix expanded as a polynomial in its 16
entries.  This is a finite analogue of `Matrix.det_fin_three` at the
next level, used here to keep the 5x5 determinant proof manageable. -/
private theorem det_fin_four_local (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.det =
      A 0 0 *
        (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2
          - A 1 2 * A 2 1 * A 3 3 + A 1 2 * A 2 3 * A 3 1
          + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1)
      - A 0 1 *
        (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2
          - A 1 2 * A 2 0 * A 3 3 + A 1 2 * A 2 3 * A 3 0
          + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0)
      + A 0 2 *
        (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1
          - A 1 1 * A 2 0 * A 3 3 + A 1 1 * A 2 3 * A 3 0
          + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0)
      - A 0 3 *
        (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1
          - A 1 1 * A 2 0 * A 3 2 + A 1 1 * A 2 2 * A 3 0
          + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero (R := ℝ) (n := 3) A]
  rw [Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.zero_succAbove,
    Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.isValue,
    pow_zero, pow_succ, one_mul, neg_mul]
  have hs2 : (Fin.succ 2 : Fin 4) = 3 := by decide
  have hsa10 : (Fin.succAbove (1 : Fin 4) 0 : Fin 4) = 0 := by decide
  have hsa11 : (Fin.succAbove (1 : Fin 4) 1 : Fin 4) = 2 := by decide
  have hsa12 : (Fin.succAbove (1 : Fin 4) 2 : Fin 4) = 3 := by decide
  have hsa20 : (Fin.succAbove (2 : Fin 4) 0 : Fin 4) = 0 := by decide
  have hsa21 : (Fin.succAbove (2 : Fin 4) 1 : Fin 4) = 1 := by decide
  have hsa22 : (Fin.succAbove (2 : Fin 4) 2 : Fin 4) = 3 := by decide
  have hsa30 : (Fin.succAbove (3 : Fin 4) 0 : Fin 4) = 0 := by decide
  have hsa31 : (Fin.succAbove (3 : Fin 4) 1 : Fin 4) = 1 := by decide
  have hsa32 : (Fin.succAbove (3 : Fin 4) 2 : Fin 4) = 2 := by decide
  rw [hs2, hsa10, hsa11, hsa12, hsa20, hsa21, hsa22, hsa30, hsa31, hsa32]
  have hval3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [hval3]
  ring

/-!
## Determinant formula for `compiledGadget α 5`
-/

/-- **Closed-form determinant of the 5×5 compiled gadget.**

For every coupling `α : ℝ`, the determinant of the 5×5 compiled gadget
`compiledGadget α 5 = α • I + L_{K_5}` equals `α * (α + 5)^4`. -/
theorem compiledGadget_5x5_det (α : ℝ) :
    (compiledGadget α 5).det = α * (α + 5)^4 := by
  set A := compiledGadget α 5 with hA
  -- Diagonal entries.
  have h00 : A (0 : Fin 5) (0 : Fin 5) = α + 4 := compiledGadget_5x5_diag α 0
  have h11 : A (1 : Fin 5) (1 : Fin 5) = α + 4 := compiledGadget_5x5_diag α 1
  have h22 : A (2 : Fin 5) (2 : Fin 5) = α + 4 := compiledGadget_5x5_diag α 2
  have h33 : A (3 : Fin 5) (3 : Fin 5) = α + 4 := compiledGadget_5x5_diag α 3
  have h44 : A (4 : Fin 5) (4 : Fin 5) = α + 4 := compiledGadget_5x5_diag α 4
  -- Distinctness facts.
  have hne01 : (0 : Fin 5) ≠ (1 : Fin 5) := by decide
  have hne02 : (0 : Fin 5) ≠ (2 : Fin 5) := by decide
  have hne03 : (0 : Fin 5) ≠ (3 : Fin 5) := by decide
  have hne04 : (0 : Fin 5) ≠ (4 : Fin 5) := by decide
  have hne10 : (1 : Fin 5) ≠ (0 : Fin 5) := by decide
  have hne12 : (1 : Fin 5) ≠ (2 : Fin 5) := by decide
  have hne13 : (1 : Fin 5) ≠ (3 : Fin 5) := by decide
  have hne14 : (1 : Fin 5) ≠ (4 : Fin 5) := by decide
  have hne20 : (2 : Fin 5) ≠ (0 : Fin 5) := by decide
  have hne21 : (2 : Fin 5) ≠ (1 : Fin 5) := by decide
  have hne23 : (2 : Fin 5) ≠ (3 : Fin 5) := by decide
  have hne24 : (2 : Fin 5) ≠ (4 : Fin 5) := by decide
  have hne30 : (3 : Fin 5) ≠ (0 : Fin 5) := by decide
  have hne31 : (3 : Fin 5) ≠ (1 : Fin 5) := by decide
  have hne32 : (3 : Fin 5) ≠ (2 : Fin 5) := by decide
  have hne34 : (3 : Fin 5) ≠ (4 : Fin 5) := by decide
  have hne40 : (4 : Fin 5) ≠ (0 : Fin 5) := by decide
  have hne41 : (4 : Fin 5) ≠ (1 : Fin 5) := by decide
  have hne42 : (4 : Fin 5) ≠ (2 : Fin 5) := by decide
  have hne43 : (4 : Fin 5) ≠ (3 : Fin 5) := by decide
  -- Off-diagonal entries.
  have h01 : A (0 : Fin 5) (1 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 0 1 hne01
  have h02 : A (0 : Fin 5) (2 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 0 2 hne02
  have h03 : A (0 : Fin 5) (3 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 0 3 hne03
  have h04 : A (0 : Fin 5) (4 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 0 4 hne04
  have h10 : A (1 : Fin 5) (0 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 1 0 hne10
  have h12 : A (1 : Fin 5) (2 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 1 2 hne12
  have h13 : A (1 : Fin 5) (3 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 1 3 hne13
  have h14 : A (1 : Fin 5) (4 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 1 4 hne14
  have h20 : A (2 : Fin 5) (0 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 2 0 hne20
  have h21 : A (2 : Fin 5) (1 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 2 1 hne21
  have h23 : A (2 : Fin 5) (3 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 2 3 hne23
  have h24 : A (2 : Fin 5) (4 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 2 4 hne24
  have h30 : A (3 : Fin 5) (0 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 3 0 hne30
  have h31 : A (3 : Fin 5) (1 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 3 1 hne31
  have h32 : A (3 : Fin 5) (2 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 3 2 hne32
  have h34 : A (3 : Fin 5) (4 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 3 4 hne34
  have h40 : A (4 : Fin 5) (0 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 4 0 hne40
  have h41 : A (4 : Fin 5) (1 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 4 1 hne41
  have h42 : A (4 : Fin 5) (2 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 4 2 hne42
  have h43 : A (4 : Fin 5) (3 : Fin 5) = -1 :=
    compiledGadget_5x5_off_diag α 4 3 hne43
  -- Cofactor expansion of 5×5 determinant along row 0.
  rw [Matrix.det_succ_row_zero (R := ℝ) (n := 4) A]
  rw [Fin.sum_univ_five]
  -- Each cofactor is a 4×4 determinant; expand each via `det_fin_four_local`.
  simp only [det_fin_four_local, Matrix.submatrix_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.zero_succAbove,
    Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.isValue,
    pow_zero, pow_succ, one_mul, neg_mul]
  -- Reduce all `Fin.succ k` and `Fin.succAbove i k` for outer (Fin 5) indices.
  have hs2 : (Fin.succ 2 : Fin 5) = 3 := by decide
  have hs3 : (Fin.succ 3 : Fin 5) = 4 := by decide
  have hsa1_0 : (Fin.succAbove (1 : Fin 5) 0 : Fin 5) = 0 := by decide
  have hsa1_1 : (Fin.succAbove (1 : Fin 5) 1 : Fin 5) = 2 := by decide
  have hsa1_2 : (Fin.succAbove (1 : Fin 5) 2 : Fin 5) = 3 := by decide
  have hsa1_3 : (Fin.succAbove (1 : Fin 5) 3 : Fin 5) = 4 := by decide
  have hsa2_0 : (Fin.succAbove (2 : Fin 5) 0 : Fin 5) = 0 := by decide
  have hsa2_1 : (Fin.succAbove (2 : Fin 5) 1 : Fin 5) = 1 := by decide
  have hsa2_2 : (Fin.succAbove (2 : Fin 5) 2 : Fin 5) = 3 := by decide
  have hsa2_3 : (Fin.succAbove (2 : Fin 5) 3 : Fin 5) = 4 := by decide
  have hsa3_0 : (Fin.succAbove (3 : Fin 5) 0 : Fin 5) = 0 := by decide
  have hsa3_1 : (Fin.succAbove (3 : Fin 5) 1 : Fin 5) = 1 := by decide
  have hsa3_2 : (Fin.succAbove (3 : Fin 5) 2 : Fin 5) = 2 := by decide
  have hsa3_3 : (Fin.succAbove (3 : Fin 5) 3 : Fin 5) = 4 := by decide
  have hsa4_0 : (Fin.succAbove (4 : Fin 5) 0 : Fin 5) = 0 := by decide
  have hsa4_1 : (Fin.succAbove (4 : Fin 5) 1 : Fin 5) = 1 := by decide
  have hsa4_2 : (Fin.succAbove (4 : Fin 5) 2 : Fin 5) = 2 := by decide
  have hsa4_3 : (Fin.succAbove (4 : Fin 5) 3 : Fin 5) = 3 := by decide
  rw [hs2, hs3,
      hsa1_0, hsa1_1, hsa1_2, hsa1_3,
      hsa2_0, hsa2_1, hsa2_2, hsa2_3,
      hsa3_0, hsa3_1, hsa3_2, hsa3_3,
      hsa4_0, hsa4_1, hsa4_2, hsa4_3]
  -- Numerical val coercions.
  have hval3_5 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have hval4_5 : ((4 : Fin 5) : ℕ) = 4 := rfl
  rw [hval3_5, hval4_5]
  -- Substitute the 25 known entries.
  rw [h00, h01, h02, h03, h04,
      h10, h11, h12, h13, h14,
      h20, h21, h22, h23, h24,
      h30, h31, h32, h33, h34,
      h40, h41, h42, h43, h44]
  ring

/-- **Determinant-equals-`1296` specialisation at `α = 1` and `n = 5`.**

Specialising `compiledGadget_5x5_det` to `α = 1` gives
`(compiledGadget 1 5).det = 1 * 6^4 = 1296`. -/
theorem compiledGadget_5x5_det_at_one :
    (compiledGadget 1 5).det = 1296 := by
  rw [compiledGadget_5x5_det]
  norm_num

/-- **Positivity of the 5×5 compiled gadget determinant for `α > 0`.** -/
theorem compiledGadget_5x5_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 5).det := by
  rw [compiledGadget_5x5_det]
  have h1 : 0 < α + 5 := by linarith
  have h2 : 0 < (α + 5)^4 := by positivity
  exact mul_pos hα h2

end PallLean.Paper93.DeepMath.PathB.Positroid

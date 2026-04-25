import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DiagonalSpec
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closed-form determinant of the 4×4 compiled gadget

We prove the explicit formula

`(compiledGadget α 4).det = α * (α + 4)^3`

for the 4×4 instantiation of the Cook–Levin compiled gadget
`compiledGadget α 4 = α • I + L_{K_4}`, which evaluates to the matrix

```
    ⎡ α + 3   −1     −1     −1   ⎤
    ⎢  −1    α + 3   −1     −1   ⎥
    ⎢  −1     −1    α + 3   −1   ⎥
    ⎣  −1     −1     −1    α + 3 ⎦
```

The eigenstructure interpretation: writing the matrix as
`(α+4) I − J` where `J` is the all-ones matrix, we see:

* The all-ones vector is an eigenvector with eigenvalue `α`
  (multiplicity 1), since `J v = 4 v` for `v = (1,1,1,1)`.
* Vectors orthogonal to the all-ones direction are eigenvectors with
  eigenvalue `α + 4` (multiplicity 3), since `J v = 0` on this subspace.

Hence `det = α · (α + 4)^3`.

The proof proceeds by:

1. Establishing the off-diagonal entry lemma
   `compiledGadget_4x4_off_diag : compiledGadget α 4 i j = -1` whenever
   `i ≠ j`, generalising the 3×3 argument from
   `CompiledGadget3x3Explicit.lean`.
2. Using `Matrix.det_succ_row_zero` to expand `det A` along the first
   row into a signed sum of four `3×3` cofactors.
3. Reducing each `3×3` cofactor via `Matrix.det_fin_three`.
4. Substituting the explicit diagonal values `α + 3` (via
   `compiledGadget_4x4_diag_4` from
   `CompiledGadget4x4DiagonalSpec.lean`) and the off-diagonal values
   `-1` for all 16 entries, then closing the polynomial identity with
   `ring`.

We additionally derive the corollary that the determinant is strictly
positive for `α > 0` (since both `α` and `(α + 4)^3` are positive).

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-!
## Off-diagonal entries of the 4×4 compiled gadget

For any `i j : Fin 4` with `i ≠ j`, we prove `compiledGadget α 4 i j = -1`.
The argument is identical to the 3×3 case in `CompiledGadget3x3Explicit`.
-/

/-- The off-diagonal entry of `completeAdj 4` is `1` whenever `i ≠ j`. -/
private lemma completeAdj_4_apply_ne {i j : Fin 4} (hij : i ≠ j) :
    completeAdj 4 i j = 1 := by
  unfold completeAdj
  simp [hij]

/-- The off-diagonal entry of the row-sum diagonal matrix
`Matrix.diagonal (rowSum (completeAdj 4))` is `0`. -/
private lemma diagonal_rowSum_completeAdj_4_off_diag
    {i j : Fin 4} (hij : i ≠ j) :
    (Matrix.diagonal (rowSum (completeAdj 4))) i j = 0 :=
  Matrix.diagonal_apply_ne _ hij

/-- **Off-diagonal entries of the 4×4 compiled gadget.**

For any `i j : Fin 4` with `i ≠ j`,
`compiledGadget α 4 i j = -1`.

The proof unfolds `compiledGadget` to `α • I + L_{K_4}`, evaluates
entrywise at `(i, j)`, and uses the off-diagonal vanishing of the
identity matrix and of `Matrix.diagonal`, together with
`completeAdj 4 i j = 1` for `i ≠ j`. -/
theorem compiledGadget_4x4_off_diag (α : ℝ) (i j : Fin 4) (hij : i ≠ j) :
    compiledGadget α 4 i j = -1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj 4)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin 4) (Fin 4) ℝ) + laplacian (completeAdj 4)) i j
        = (α • (1 : Matrix (Fin 4) (Fin 4) ℝ)) i j
          + (laplacian (completeAdj 4)) i j := rfl
  rw [hadd]
  -- `(α • I) i j = α • (I i j) = α • 0 = 0` since `i ≠ j`.
  have hsmul :
      (α • (1 : Matrix (Fin 4) (Fin 4) ℝ)) i j = 0 := by
    show α • ((1 : Matrix (Fin 4) (Fin 4) ℝ) i j) = 0
    rw [Matrix.one_apply_ne hij]
    simp
  rw [hsmul]
  -- `(L_{K_4}) i j = (diagonal (rowSum A)) i j - A i j = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj 4)) i j = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj 4)) - completeAdj 4) i j
          = (Matrix.diagonal (rowSum (completeAdj 4))) i j
              - (completeAdj 4) i j := rfl
    rw [hsub, diagonal_rowSum_completeAdj_4_off_diag hij,
        completeAdj_4_apply_ne hij]
    ring
  rw [hlap]
  ring

/-!
## Determinant formula via cofactor expansion

The strategy: expand the determinant along row 0 using
`Matrix.det_succ_row_zero`, reducing the 4×4 determinant to a signed
sum of four 3×3 cofactors. Each 3×3 cofactor is then expanded using
`Matrix.det_fin_three`. After substituting all 16 entries via the
diagonal/off-diagonal lemmas, `ring` closes the resulting polynomial
identity in `α`.
-/

/-- **Closed-form determinant of the 4×4 compiled gadget.**

For every coupling `α : ℝ`, the determinant of the 4×4 compiled gadget
`compiledGadget α 4 = α • I + L_{K_4}` equals `α * (α + 4)^3`.

Equivalently,
`det = (α + 3)^4 − 6(α + 3)^2 − 8(α + 3) − 3 = α^4 + 12α^3 + 48α^2 + 64α`.

The proof uses `Matrix.det_succ_row_zero` to expand the determinant
along row 0, reducing to four signed 3×3 cofactors. Each cofactor is
expanded via `Matrix.det_fin_three`. After substituting the 4 diagonal
entries `α + 3` (via `compiledGadget_4x4_diag_4`) and the 12
off-diagonal entries `-1` (via `compiledGadget_4x4_off_diag`), the
identity `(α+3)^4 − 6(α+3)^2 − 8(α+3) − 3 = α(α+4)^3` is closed by
`ring`. -/
theorem compiledGadget_4x4_det (α : ℝ) :
    (compiledGadget α 4).det = α * (α + 4)^3 := by
  -- Step 1: introduce abbreviations for the 16 entries.
  set A := compiledGadget α 4 with hA
  -- Diagonal entries: α + 3.
  have h00 : A (0 : Fin 4) (0 : Fin 4) = α + 3 := compiledGadget_4x4_diag_4 α 0
  have h11 : A (1 : Fin 4) (1 : Fin 4) = α + 3 := compiledGadget_4x4_diag_4 α 1
  have h22 : A (2 : Fin 4) (2 : Fin 4) = α + 3 := compiledGadget_4x4_diag_4 α 2
  have h33 : A (3 : Fin 4) (3 : Fin 4) = α + 3 := compiledGadget_4x4_diag_4 α 3
  -- Distinctness facts for off-diagonal positions.
  have hne01 : (0 : Fin 4) ≠ (1 : Fin 4) := by decide
  have hne02 : (0 : Fin 4) ≠ (2 : Fin 4) := by decide
  have hne03 : (0 : Fin 4) ≠ (3 : Fin 4) := by decide
  have hne10 : (1 : Fin 4) ≠ (0 : Fin 4) := by decide
  have hne12 : (1 : Fin 4) ≠ (2 : Fin 4) := by decide
  have hne13 : (1 : Fin 4) ≠ (3 : Fin 4) := by decide
  have hne20 : (2 : Fin 4) ≠ (0 : Fin 4) := by decide
  have hne21 : (2 : Fin 4) ≠ (1 : Fin 4) := by decide
  have hne23 : (2 : Fin 4) ≠ (3 : Fin 4) := by decide
  have hne30 : (3 : Fin 4) ≠ (0 : Fin 4) := by decide
  have hne31 : (3 : Fin 4) ≠ (1 : Fin 4) := by decide
  have hne32 : (3 : Fin 4) ≠ (2 : Fin 4) := by decide
  -- Off-diagonal entries: -1.
  have h01 : A (0 : Fin 4) (1 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 0 1 hne01
  have h02 : A (0 : Fin 4) (2 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 0 2 hne02
  have h03 : A (0 : Fin 4) (3 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 0 3 hne03
  have h10 : A (1 : Fin 4) (0 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 1 0 hne10
  have h12 : A (1 : Fin 4) (2 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 1 2 hne12
  have h13 : A (1 : Fin 4) (3 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 1 3 hne13
  have h20 : A (2 : Fin 4) (0 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 2 0 hne20
  have h21 : A (2 : Fin 4) (1 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 2 1 hne21
  have h23 : A (2 : Fin 4) (3 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 2 3 hne23
  have h30 : A (3 : Fin 4) (0 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 3 0 hne30
  have h31 : A (3 : Fin 4) (1 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 3 1 hne31
  have h32 : A (3 : Fin 4) (2 : Fin 4) = -1 := compiledGadget_4x4_off_diag α 3 2 hne32
  -- Step 2: cofactor expansion along row 0.
  -- det A = Σ_{j : Fin 4} (-1)^j * A 0 j * det (A.submatrix Fin.succ j.succAbove).
  rw [Matrix.det_succ_row_zero (R := ℝ) (n := 3) A]
  -- Step 3: expand the sum over Fin 4 explicitly.
  rw [Fin.sum_univ_four]
  -- Step 4: simplify (-1)^j and the entries A 0 j.
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.zero_succAbove,
    Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.isValue,
    pow_zero, pow_succ, one_mul, neg_mul]
  -- Step 5: normalise the remaining `Fin.succ 2` and `Fin.succAbove _ _` terms
  -- to explicit `Fin 4` values.  Each is a closed numeric fact provable by `decide`.
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
  -- Step 6: substitute the 16 known entries.
  rw [h00, h01, h02, h03,
      h10, h11, h12, h13,
      h20, h21, h22, h23,
      h30, h31, h32, h33]
  -- Step 7: normalise the residual `(-1)^↑3` term (which is `(-1)^3 = -1`).
  have hval3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [hval3]
  -- Goal now contains `(-1 : ℝ) ^ (3 : ℕ)`, which `ring` handles.
  ring

/-- **Determinant-equals-`125` specialisation at `α = 1` and `n = 4`.**

Specialising `compiledGadget_4x4_det` to `α = 1` gives
`(compiledGadget 1 4).det = 1 * 5^3 = 125`. -/
theorem compiledGadget_4x4_det_at_one :
    (compiledGadget 1 4).det = 125 := by
  rw [compiledGadget_4x4_det]
  norm_num

/-- **Positivity of the 4×4 compiled gadget determinant for `α > 0`.**

For every coupling `α > 0`, the determinant of `compiledGadget α 4`
is strictly positive.

This follows from the closed-form `det = α * (α + 4)^3`: the factor
`α` is positive by hypothesis, and `(α + 4)^3 > 0` since `α + 4 > 4 > 0`
(so its cube is a positive real). -/
theorem compiledGadget_4x4_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 4).det := by
  rw [compiledGadget_4x4_det]
  have h1 : 0 < α + 4 := by linarith
  have h2 : 0 < (α + 4)^3 := by positivity
  exact mul_pos hα h2

end PallLean.Paper93.DeepMath.PathB.Positroid

import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetSmallNDiagonals
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 4000000

/-!
# Closed-form determinant of the 8×8 compiled gadget (symbolic in `α`)

We prove the explicit formula

`(compiledGadget α 8).det = α * (α + 8)^7`

for the 8×8 instantiation of the Cook–Levin compiled gadget
`compiledGadget α 8 = α • I + L_{K_8}`, which evaluates to the matrix

```
    ⎡ α + 7   −1    −1    −1    −1    −1    −1    −1   ⎤
    ⎢  −1   α + 7   −1    −1    −1    −1    −1    −1   ⎥
    ⎢  −1    −1   α + 7   −1    −1    −1    −1    −1   ⎥
    ⎢  −1    −1    −1   α + 7   −1    −1    −1    −1   ⎥
    ⎢  −1    −1    −1    −1   α + 7   −1    −1    −1   ⎥
    ⎢  −1    −1    −1    −1    −1   α + 7   −1    −1   ⎥
    ⎢  −1    −1    −1    −1    −1    −1   α + 7   −1   ⎥
    ⎣  −1    −1    −1    −1    −1    −1    −1   α + 7  ⎦
```

This is the `n = 8` instance of the general formula
`det(α • I + L_{K_n}) = α · (α + n)^{n−1}` from the eigenstructure of
the complete-graph Laplacian: the all-ones vector is an eigenvector
with eigenvalue `α`, and the orthogonal complement of zero-sum vectors
is an `(n−1)`-dimensional eigenspace with eigenvalue `α + n`.

We additionally derive:

* `compiledGadget_8x8_det_at_one`: at `α = 1`, the determinant
  evaluates to `1 · 9^7 = 4782969`.
* `compiledGadget_8x8_det_pos`: positivity for `α > 0`.

The proof strategy mirrors `CompiledGadget6x6DetConcrete.lean`: we
first show that `compiledGadget α 8` equals an explicit matrix
`!![α+7, -1, …; …]` by case analysis on the entries (diagonal vs
off-diagonal), then expand the determinant using `Matrix.det_succ_row_zero`
recursively (via `simp`) until reaching the base case, and close the
resulting polynomial identity with `ring`.

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
## Off-diagonal entries of the 8×8 compiled gadget

For any `i j : Fin 8` with `i ≠ j`, we prove `compiledGadget α 8 i j = -1`.
The proof unfolds `compiledGadget` to `α • I + L_{K_8}`, evaluates
entrywise at `(i, j)`, and uses the off-diagonal vanishing of the
identity matrix and of `Matrix.diagonal`, together with
`completeAdj 8 i j = 1` for `i ≠ j`.
-/

/-- **Off-diagonal entries of the 8×8 compiled gadget.**

For any `i j : Fin 8` with `i ≠ j`,
`compiledGadget α 8 i j = -1`.

The proof is identical in structure to the 6×6 version. Unfold
`compiledGadget α 8` to `α • I + L_{K_8}`, evaluate entrywise at `(i, j)`:
the smul-by-α term vanishes (since the identity off-diagonal is `0`),
and the Laplacian off-diagonal equals
`(diagonal (rowSum A)) i j - A i j = 0 - 1 = -1`. -/
theorem compiledGadget_8x8_off_diag (α : ℝ) (i j : Fin 8) (hij : i ≠ j) :
    compiledGadget α 8 i j = -1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj 8)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin 8) (Fin 8) ℝ) + laplacian (completeAdj 8)) i j
        = (α • (1 : Matrix (Fin 8) (Fin 8) ℝ)) i j
          + (laplacian (completeAdj 8)) i j := rfl
  rw [hadd]
  -- `(α • I) i j = α • (I i j) = α • 0 = 0` since `i ≠ j`.
  have hsmul :
      (α • (1 : Matrix (Fin 8) (Fin 8) ℝ)) i j = 0 := by
    show α • ((1 : Matrix (Fin 8) (Fin 8) ℝ) i j) = 0
    rw [Matrix.one_apply_ne hij]
    simp
  rw [hsmul]
  -- `(L_{K_8}) i j = (diagonal (rowSum A)) i j - A i j = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj 8)) i j = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj 8)) - completeAdj 8) i j
          = (Matrix.diagonal (rowSum (completeAdj 8))) i j
              - (completeAdj 8) i j := rfl
    rw [hsub, Matrix.diagonal_apply_ne _ hij]
    have hca : completeAdj 8 i j = 1 := by
      unfold completeAdj
      simp [hij]
    rw [hca]
    ring
  rw [hlap]
  ring

/-!
## Explicit matrix form

We show that `compiledGadget α 8` agrees entrywise with the explicit
8×8 matrix literal whose diagonal entries are `α + 7` and whose
off-diagonal entries are `-1`. This reduces determinant calculations
to a pure cofactor expansion on a fully concrete matrix.
-/

/-- **Explicit matrix form of the 8×8 compiled gadget.**

The 8×8 compiled gadget `compiledGadget α 8` is entrywise equal to the
explicit matrix
`!![α+7, -1, -1, -1, -1, -1, -1, -1; …; -1, …, -1, α+7]`.

The proof proceeds by `Matrix.ext` and case analysis on whether the row
and column indices coincide:

* On the diagonal `i = j`: use `compiledGadget_8x8_diag` to get `α + 7`,
  then `fin_cases i` to identify the corresponding entry of the matrix
  literal (which is `α + 7` in each diagonal slot).
* Off the diagonal `i ≠ j`: use `compiledGadget_8x8_off_diag` to get
  `-1`, then `fin_cases` on both `i` and `j` to verify each of the 56
  off-diagonal entries of the matrix literal is `-1`. -/
theorem compiledGadget_8x8_eq_explicit (α : ℝ) :
    compiledGadget α 8 =
      (!![α + 7, -1, -1, -1, -1, -1, -1, -1;
          -1, α + 7, -1, -1, -1, -1, -1, -1;
          -1, -1, α + 7, -1, -1, -1, -1, -1;
          -1, -1, -1, α + 7, -1, -1, -1, -1;
          -1, -1, -1, -1, α + 7, -1, -1, -1;
          -1, -1, -1, -1, -1, α + 7, -1, -1;
          -1, -1, -1, -1, -1, -1, α + 7, -1;
          -1, -1, -1, -1, -1, -1, -1, α + 7] : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  by_cases h : i = j
  · -- Diagonal case: both sides equal `α + 7`.
    subst h
    rw [compiledGadget_8x8_diag]
    fin_cases i <;> rfl
  · -- Off-diagonal case: both sides equal `-1`.
    rw [compiledGadget_8x8_off_diag α i j h]
    fin_cases i <;> fin_cases j <;>
      first | rfl | (exfalso; exact h rfl)

/-!
## Determinant formula via repeated cofactor expansion

The strategy: rewrite `compiledGadget α 8` to its explicit matrix form,
then expand the determinant repeatedly via `Matrix.det_succ_row_zero`,
unfolding `Fin.sum_univ_succ`, `Matrix.submatrix_apply`, and
`Fin.succAbove` to evaluate the matrix-literal entries inside each
cofactor. After seven levels of recursion, all sub-determinants reduce
to closed expressions in `α`, and `ring` closes the polynomial identity
`(α+7)^8 - … = α(α+8)^7`.
-/

/-- **Closed-form determinant of the 8×8 compiled gadget.**

For every coupling `α : ℝ`, the determinant of the 8×8 compiled gadget
`compiledGadget α 8 = α • I + L_{K_8}` equals `α * (α + 8)^7`.

This is the `n = 8` instance of the general eigenstructure-based
formula `det(α • I + L_{K_n}) = α · (α + n)^{n−1}`, proved here by a
direct cofactor expansion on the explicit `8×8` matrix literal.

The eigenvalue interpretation:

* the all-ones vector `(1, 1, 1, 1, 1, 1, 1, 1)` is an eigenvector with
  eigenvalue `α` (since `J · 1 = 8 · 1` and `α · I + L = α · I + 8I − J`);
* the 7-dimensional zero-sum subspace is an eigenspace with
  eigenvalue `α + 8`. -/
theorem compiledGadget_8x8_det (α : ℝ) :
    (compiledGadget α 8).det = α * (α + 8)^7 := by
  rw [compiledGadget_8x8_eq_explicit]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
        Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- **Determinant-equals-`4782969` specialisation at `α = 1` and `n = 8`.**

Specialising `compiledGadget_8x8_det` to `α = 1` gives
`(compiledGadget 1 8).det = 1 * 9^7 = 4782969`. This is the `n = 8`
witness of the closed-form pattern `det = α(α+n)^{n−1}` evaluated at
the gauge-distinguished coupling `α = 1`. -/
theorem compiledGadget_8x8_det_at_one :
    (compiledGadget 1 8).det = 4782969 := by
  rw [compiledGadget_8x8_det]
  norm_num

/-- **Positivity of the 8×8 compiled gadget determinant for `α > 0`.**

For every coupling `α > 0`, the determinant of `compiledGadget α 8`
is strictly positive.

This follows from the closed-form `det = α * (α + 8)^7`: the factor
`α` is positive by hypothesis, and `(α + 8)^7 > 0` since `α + 8 > 8 > 0`
(so its odd power is a positive real). -/
theorem compiledGadget_8x8_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 8).det := by
  rw [compiledGadget_8x8_det]
  have h1 : 0 < α + 8 := by linarith
  have h2 : 0 < (α + 8)^7 := by positivity
  exact mul_pos hα h2

end PallLean.Paper93.DeepMath.PathB.Positroid

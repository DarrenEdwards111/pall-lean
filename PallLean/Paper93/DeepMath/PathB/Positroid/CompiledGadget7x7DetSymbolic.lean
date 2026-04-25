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

/-!
# Closed-form determinant of the 7×7 compiled gadget (symbolic)

We prove the explicit formula

`(compiledGadget α 7).det = α * (α + 7)^6`

for the 7×7 instantiation of the Cook–Levin compiled gadget
`compiledGadget α 7 = α • I + L_{K_7}`, which evaluates to the matrix

```
    ⎡ α + 6   −1     −1     −1     −1     −1     −1   ⎤
    ⎢  −1    α + 6   −1     −1     −1     −1     −1   ⎥
    ⎢  −1     −1    α + 6   −1     −1     −1     −1   ⎥
    ⎢  −1     −1     −1    α + 6   −1     −1     −1   ⎥
    ⎢  −1     −1     −1     −1    α + 6   −1     −1   ⎥
    ⎢  −1     −1     −1     −1     −1    α + 6   −1   ⎥
    ⎣  −1     −1     −1     −1     −1     −1    α + 6 ⎦
```

This is the `n = 7` instance of the general formula
`det(α • I + L_{K_n}) = α · (α + n)^{n−1}` from the eigenstructure of
the complete-graph Laplacian: the all-ones vector is an eigenvector
with eigenvalue `α`, and the orthogonal complement of zero-sum vectors
is a `(n−1)`-dimensional eigenspace with eigenvalue `α + n`.

We additionally derive:

* `compiledGadget_7x7_det_at_one`: at `α = 1`, the determinant
  evaluates to `1 · 8^6 = 262144`.
* `compiledGadget_7x7_det_pos`: positivity for `α > 0`.

The proof strategy mirrors `CompiledGadget6x6DetConcrete.lean` exactly:
we first show that `compiledGadget α 7` equals an explicit matrix
literal `!![α+6, -1, …; …]` by case analysis on the entries (diagonal
vs off-diagonal), then expand the determinant using
`Matrix.det_succ_row_zero` recursively (via `simp`) until reaching the
base case, and close the resulting polynomial identity with `ring`.

Because `n = 7` produces a noticeably larger cofactor expansion than
`n = 6` (the recursive `det_succ_row_zero` blow-up is `7! = 5040`
signed leaf terms versus `6! = 720`), we raise the heartbeat budget
locally with `set_option maxHeartbeats 1000000`.

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
## Off-diagonal entries of the 7×7 compiled gadget

For any `i j : Fin 7` with `i ≠ j`, we prove `compiledGadget α 7 i j = -1`.
The proof unfolds `compiledGadget` to `α • I + L_{K_7}`, evaluates
entrywise at `(i, j)`, and uses the off-diagonal vanishing of the
identity matrix and of `Matrix.diagonal`, together with
`completeAdj 7 i j = 1` for `i ≠ j`.
-/

/-- **Off-diagonal entries of the 7×7 compiled gadget.**

For any `i j : Fin 7` with `i ≠ j`,
`compiledGadget α 7 i j = -1`.

The proof is identical in structure to the 6×6 version. Unfold
`compiledGadget α 7` to `α • I + L_{K_7}`, evaluate entrywise at `(i, j)`:
the smul-by-α term vanishes (since the identity off-diagonal is `0`),
and the Laplacian off-diagonal equals
`(diagonal (rowSum A)) i j - A i j = 0 - 1 = -1`. -/
theorem compiledGadget_7x7_off_diag (α : ℝ) (i j : Fin 7) (hij : i ≠ j) :
    compiledGadget α 7 i j = -1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj 7)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin 7) (Fin 7) ℝ) + laplacian (completeAdj 7)) i j
        = (α • (1 : Matrix (Fin 7) (Fin 7) ℝ)) i j
          + (laplacian (completeAdj 7)) i j := rfl
  rw [hadd]
  -- `(α • I) i j = α • (I i j) = α • 0 = 0` since `i ≠ j`.
  have hsmul :
      (α • (1 : Matrix (Fin 7) (Fin 7) ℝ)) i j = 0 := by
    show α • ((1 : Matrix (Fin 7) (Fin 7) ℝ) i j) = 0
    rw [Matrix.one_apply_ne hij]
    simp
  rw [hsmul]
  -- `(L_{K_7}) i j = (diagonal (rowSum A)) i j - A i j = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj 7)) i j = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj 7)) - completeAdj 7) i j
          = (Matrix.diagonal (rowSum (completeAdj 7))) i j
              - (completeAdj 7) i j := rfl
    rw [hsub, Matrix.diagonal_apply_ne _ hij]
    have hca : completeAdj 7 i j = 1 := by
      unfold completeAdj
      simp [hij]
    rw [hca]
    ring
  rw [hlap]
  ring

/-!
## Explicit matrix form

We show that `compiledGadget α 7` agrees entrywise with the explicit
7×7 matrix literal whose diagonal entries are `α + 6` and whose
off-diagonal entries are `-1`. This reduces determinant calculations
to a pure cofactor expansion on a fully concrete matrix.
-/

/-- **Explicit matrix form of the 7×7 compiled gadget.**

The 7×7 compiled gadget `compiledGadget α 7` is entrywise equal to the
explicit matrix `!![α+6, -1, …, -1; …; -1, …, -1, α+6]`.

The proof proceeds by `Matrix.ext` and case analysis on whether the row
and column indices coincide:

* On the diagonal `i = j`: use `compiledGadget_7x7_diag` to get `α + 6`,
  then `fin_cases i` to identify the corresponding entry of the matrix
  literal (which is `α + 6` in each diagonal slot).
* Off the diagonal `i ≠ j`: use `compiledGadget_7x7_off_diag` to get
  `-1`, then `fin_cases` on both `i` and `j` to verify each of the 42
  off-diagonal entries of the matrix literal is `-1`. -/
theorem compiledGadget_7x7_eq_explicit (α : ℝ) :
    compiledGadget α 7 =
      (!![α + 6, -1, -1, -1, -1, -1, -1;
          -1, α + 6, -1, -1, -1, -1, -1;
          -1, -1, α + 6, -1, -1, -1, -1;
          -1, -1, -1, α + 6, -1, -1, -1;
          -1, -1, -1, -1, α + 6, -1, -1;
          -1, -1, -1, -1, -1, α + 6, -1;
          -1, -1, -1, -1, -1, -1, α + 6] : Matrix (Fin 7) (Fin 7) ℝ) := by
  ext i j
  by_cases h : i = j
  · -- Diagonal case: both sides equal `α + 6`.
    subst h
    rw [compiledGadget_7x7_diag]
    fin_cases i <;> rfl
  · -- Off-diagonal case: both sides equal `-1`.
    rw [compiledGadget_7x7_off_diag α i j h]
    fin_cases i <;> fin_cases j <;>
      first | rfl | (exfalso; exact h rfl)

/-!
## Determinant formula via repeated cofactor expansion

The strategy: rewrite `compiledGadget α 7` to its explicit matrix form,
then expand the determinant repeatedly via `Matrix.det_succ_row_zero`,
unfolding `Fin.sum_univ_succ`, `Matrix.submatrix_apply`, and
`Fin.succAbove` to evaluate the matrix-literal entries inside each
cofactor. After full recursion (depth 7), all sub-determinants reduce
to closed expressions in `α`, and `ring` closes the polynomial identity
`(α+6)^7 - 21(α+6)^5 + … = α(α+6)^6`.
-/

set_option maxHeartbeats 1000000 in
/-- **Closed-form determinant of the 7×7 compiled gadget.**

For every coupling `α : ℝ`, the determinant of the 7×7 compiled gadget
`compiledGadget α 7 = α • I + L_{K_7}` equals `α * (α + 7)^6`.

This is the `n = 7` instance of the general eigenstructure-based
formula `det(α • I + L_{K_n}) = α · (α + n)^{n−1}`, proved here by a
direct cofactor expansion on the explicit `7×7` matrix literal.

The eigenvalue interpretation:

* the all-ones vector `(1, 1, 1, 1, 1, 1, 1)` is an eigenvector with
  eigenvalue `α` (since `J · 1 = 7 · 1` and `α · I + L = α · I + 7I − J`);
* the 6-dimensional zero-sum subspace is an eigenspace with
  eigenvalue `α + 7`. -/
theorem compiledGadget_7x7_det (α : ℝ) :
    (compiledGadget α 7).det = α * (α + 7)^6 := by
  rw [compiledGadget_7x7_eq_explicit]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
        Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- **Determinant-equals-`262144` specialisation at `α = 1` and `n = 7`.**

Specialising `compiledGadget_7x7_det` to `α = 1` gives
`(compiledGadget 1 7).det = 1 * 8^6 = 262144`. This is the `n = 7`
witness of the closed-form pattern `det = α(α+n)^{n−1}` evaluated at
the gauge-distinguished coupling `α = 1`. -/
theorem compiledGadget_7x7_det_at_one :
    (compiledGadget 1 7).det = 262144 := by
  rw [compiledGadget_7x7_det]
  norm_num

/-- **Positivity of the 7×7 compiled gadget determinant for `α > 0`.**

For every coupling `α > 0`, the determinant of `compiledGadget α 7`
is strictly positive.

This follows from the closed-form `det = α * (α + 7)^6`: the factor
`α` is positive by hypothesis, and `(α + 7)^6 > 0` since `α + 7 > 7 > 0`
(so its even power is a positive real). -/
theorem compiledGadget_7x7_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 7).det := by
  rw [compiledGadget_7x7_det]
  have h1 : 0 < α + 7 := by linarith
  have h2 : 0 < (α + 7)^6 := by positivity
  exact mul_pos hα h2

end PallLean.Paper93.DeepMath.PathB.Positroid

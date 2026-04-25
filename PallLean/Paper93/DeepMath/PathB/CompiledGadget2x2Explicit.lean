import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Explicit form of the 2×2 compiled gadget matrix entries

We give the explicit values of every entry of `compiledGadget α 2`:

* `compiledGadget α 2 i i = α + 1` for the diagonal,
* `compiledGadget α 2 0 1 = -1` for the (0,1) off-diagonal entry,
* `compiledGadget α 2 1 0 = -1` for the (1,0) off-diagonal entry.

Together these say that
`compiledGadget α 2 = ![![α + 1, -1], ![-1, α + 1]]`,
which is the smallest non-trivial Laplacian-shifted gadget.

The diagonal value follows immediately from `compiledGadget_diagonal`
(`α + ((2 : ℝ) - 1) = α + 1`).  The off-diagonal values are obtained
by directly unfolding `compiledGadget` to `α • I + L_{K_2}` and noting
that:

* the off-diagonal of the identity matrix is zero,
* the off-diagonal of any matrix of the form `Matrix.diagonal d` is
  zero,
* `completeAdj 2 0 1 = completeAdj 2 1 0 = 1` (since `0 ≠ 1` in
  `Fin 2`).

Thus `(α • I + L_{K_2}) i j = 0 + (0 - 1) = -1` for `i ≠ j`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **Diagonal entries of the 2×2 compiled gadget.**

For every index `i : Fin 2`,
`(compiledGadget α 2) i i = α + 1`.

This is an immediate corollary of `compiledGadget_diagonal`, since
`α + ((2 : ℝ) - 1) = α + 1`. -/
theorem compiledGadget_2x2_diag (α : ℝ) (i : Fin 2) :
    compiledGadget α 2 i i = α + 1 := by
  rw [compiledGadget_diagonal]
  ring

/-- The (0,1) off-diagonal entry of `completeAdj 2` is `1`.
This is the basic fact that `0 ≠ 1` in `Fin 2`, plugged into the
definition of `completeAdj`. -/
private lemma completeAdj_2_zero_one : completeAdj 2 (0 : Fin 2) (1 : Fin 2) = 1 := by
  unfold completeAdj
  have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  simp [h]

/-- The (1,0) off-diagonal entry of `completeAdj 2` is `1`. -/
private lemma completeAdj_2_one_zero : completeAdj 2 (1 : Fin 2) (0 : Fin 2) = 1 := by
  unfold completeAdj
  have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  simp [h]

/-- The (0,1) entry of the row-sum diagonal of `completeAdj 2` is `0`,
because the off-diagonal of any matrix of the form
`Matrix.diagonal d` vanishes. -/
private lemma diagonal_rowSum_completeAdj_2_zero_one :
    (Matrix.diagonal (rowSum (completeAdj 2))) (0 : Fin 2) (1 : Fin 2) = 0 := by
  have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  exact Matrix.diagonal_apply_ne _ h

/-- The (1,0) entry of the row-sum diagonal of `completeAdj 2` is `0`. -/
private lemma diagonal_rowSum_completeAdj_2_one_zero :
    (Matrix.diagonal (rowSum (completeAdj 2))) (1 : Fin 2) (0 : Fin 2) = 0 := by
  have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  exact Matrix.diagonal_apply_ne _ h

/-- The (0,1) entry of the identity matrix is `0`. -/
private lemma one_apply_zero_one_fin2 :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 2) (1 : Fin 2) = 0 := by
  have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  exact Matrix.one_apply_ne h

/-- The (1,0) entry of the identity matrix is `0`. -/
private lemma one_apply_one_zero_fin2 :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Fin 2) (0 : Fin 2) = 0 := by
  have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  exact Matrix.one_apply_ne h

/-- **(0,1) off-diagonal entry of the 2×2 compiled gadget.**

`compiledGadget α 2 0 1 = -1`.

The proof unfolds `compiledGadget` to `α • I + L_{K_2}`, evaluates
entrywise at `(0,1)`, and uses the off-diagonal vanishing of the
identity matrix together with `(L_{K_2}) 0 1 = 0 - 1 = -1`. -/
theorem compiledGadget_2x2_off_diag_01 (α : ℝ) :
    compiledGadget α 2 (0 : Fin 2) (1 : Fin 2) = -1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj 2)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + laplacian (completeAdj 2))
          (0 : Fin 2) (1 : Fin 2)
        = (α • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (0 : Fin 2) (1 : Fin 2)
          + (laplacian (completeAdj 2)) (0 : Fin 2) (1 : Fin 2) := rfl
  rw [hadd]
  -- `(α • I) 0 1 = α • (I 0 1) = α • 0 = 0`.
  have hsmul :
      (α • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (0 : Fin 2) (1 : Fin 2) = 0 := by
    show α • ((1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 2) (1 : Fin 2)) = 0
    rw [one_apply_zero_one_fin2]
    simp
  rw [hsmul]
  -- `(L_{K_2}) 0 1 = (diagonal (rowSum A)) 0 1 - A 0 1 = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj 2)) (0 : Fin 2) (1 : Fin 2) = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj 2)) - completeAdj 2)
              (0 : Fin 2) (1 : Fin 2)
          = (Matrix.diagonal (rowSum (completeAdj 2))) (0 : Fin 2) (1 : Fin 2)
              - (completeAdj 2) (0 : Fin 2) (1 : Fin 2) := rfl
    rw [hsub, diagonal_rowSum_completeAdj_2_zero_one, completeAdj_2_zero_one]
    ring
  rw [hlap]
  ring

/-- **(1,0) off-diagonal entry of the 2×2 compiled gadget.**

`compiledGadget α 2 1 0 = -1`.

Same argument as `compiledGadget_2x2_off_diag_01` with the indices
swapped; the off-diagonal of `α • I` and of `Matrix.diagonal` both
vanish at `(1,0)`, and `completeAdj 2 1 0 = 1`. -/
theorem compiledGadget_2x2_off_diag_10 (α : ℝ) :
    compiledGadget α 2 (1 : Fin 2) (0 : Fin 2) = -1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj 2)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + laplacian (completeAdj 2))
          (1 : Fin 2) (0 : Fin 2)
        = (α • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (1 : Fin 2) (0 : Fin 2)
          + (laplacian (completeAdj 2)) (1 : Fin 2) (0 : Fin 2) := rfl
  rw [hadd]
  -- `(α • I) 1 0 = α • (I 1 0) = α • 0 = 0`.
  have hsmul :
      (α • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (1 : Fin 2) (0 : Fin 2) = 0 := by
    show α • ((1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Fin 2) (0 : Fin 2)) = 0
    rw [one_apply_one_zero_fin2]
    simp
  rw [hsmul]
  -- `(L_{K_2}) 1 0 = (diagonal (rowSum A)) 1 0 - A 1 0 = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj 2)) (1 : Fin 2) (0 : Fin 2) = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj 2)) - completeAdj 2)
              (1 : Fin 2) (0 : Fin 2)
          = (Matrix.diagonal (rowSum (completeAdj 2))) (1 : Fin 2) (0 : Fin 2)
              - (completeAdj 2) (1 : Fin 2) (0 : Fin 2) := rfl
    rw [hsub, diagonal_rowSum_completeAdj_2_one_zero, completeAdj_2_one_zero]
    ring
  rw [hlap]
  ring

end PallLean.Paper93.DeepMath.PathB

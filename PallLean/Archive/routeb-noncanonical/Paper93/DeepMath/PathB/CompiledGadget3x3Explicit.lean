import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Explicit form of the 3×3 compiled gadget matrix entries

We give the explicit values of every entry of `compiledGadget α 3`:

* `compiledGadget α 3 i i = α + 2` for the diagonal,
* `compiledGadget α 3 i j = -1` for the off-diagonal entries
  (i.e. whenever `i ≠ j` in `Fin 3`).

Together these say that
`compiledGadget α 3 = ![![α + 2, -1, -1], ![-1, α + 2, -1], ![-1, -1, α + 2]]`,
the §28.3 compiled gadget on the complete graph `K_3`.

The diagonal value follows immediately from `compiledGadget_diagonal`
(`α + ((3 : ℝ) - 1) = α + 2`).  The off-diagonal values are obtained
by directly unfolding `compiledGadget` to `α • I + L_{K_3}` and noting
that:

* the off-diagonal of the identity matrix is zero,
* the off-diagonal of any matrix of the form `Matrix.diagonal d` is
  zero,
* `completeAdj 3 i j = 1` whenever `i ≠ j`.

Thus `(α • I + L_{K_3}) i j = 0 + (0 - 1) = -1` for `i ≠ j`.

We also derive the trace as a corollary of `compiledGadget_trace_formula`,
which evaluates to `3 * α + 6`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **Diagonal entries of the 3×3 compiled gadget.**

For every index `i : Fin 3`,
`(compiledGadget α 3) i i = α + 2`.

This is an immediate corollary of `compiledGadget_diagonal`, since
`α + ((3 : ℝ) - 1) = α + 2`. -/
theorem compiledGadget_3x3_diag (α : ℝ) (i : Fin 3) :
    compiledGadget α 3 i i = α + 2 := by
  rw [compiledGadget_diagonal]
  ring

/-- The off-diagonal entry of `completeAdj n` is `1` whenever `i ≠ j`.
This is just the definition of `completeAdj`: it is `if i = j then 0 else 1`. -/
private lemma completeAdj_apply_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    completeAdj n i j = 1 := by
  unfold completeAdj
  simp [hij]

/-- The off-diagonal entry of the row-sum diagonal matrix
`Matrix.diagonal (rowSum (completeAdj 3))` is `0`, because the
off-diagonal of any matrix of the form `Matrix.diagonal d` vanishes. -/
private lemma diagonal_rowSum_completeAdj_3_off_diag
    {i j : Fin 3} (hij : i ≠ j) :
    (Matrix.diagonal (rowSum (completeAdj 3))) i j = 0 :=
  Matrix.diagonal_apply_ne _ hij

/-- **Off-diagonal entries of the 3×3 compiled gadget.**

For any `i j : Fin 3` with `i ≠ j`,
`compiledGadget α 3 i j = -1`.

The proof unfolds `compiledGadget` to `α • I + L_{K_3}`, evaluates
entrywise at `(i, j)`, and uses the off-diagonal vanishing of the
identity matrix and of `Matrix.diagonal`, together with
`completeAdj 3 i j = 1` for `i ≠ j`. -/
theorem compiledGadget_3x3_off_diag (α : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    compiledGadget α 3 i j = -1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj 3)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin 3) (Fin 3) ℝ) + laplacian (completeAdj 3)) i j
        = (α • (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j
          + (laplacian (completeAdj 3)) i j := rfl
  rw [hadd]
  -- `(α • I) i j = α • (I i j) = α • 0 = 0` since `i ≠ j`.
  have hsmul :
      (α • (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j = 0 := by
    show α • ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j) = 0
    rw [Matrix.one_apply_ne hij]
    simp
  rw [hsmul]
  -- `(L_{K_3}) i j = (diagonal (rowSum A)) i j - A i j = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj 3)) i j = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj 3)) - completeAdj 3) i j
          = (Matrix.diagonal (rowSum (completeAdj 3))) i j
              - (completeAdj 3) i j := rfl
    rw [hsub, diagonal_rowSum_completeAdj_3_off_diag hij,
        completeAdj_apply_ne hij]
    ring
  rw [hlap]
  ring

/-- **Trace of the 3×3 compiled gadget.**

`trace (compiledGadget α 3) = 3 * α + 6`.

This is an immediate corollary of `compiledGadget_trace_formula`, since
`(3 : ℝ) * α + (3 : ℝ) * ((3 : ℝ) - 1) = 3 * α + 6`. -/
theorem compiledGadget_3x3_trace (α : ℝ) :
    (compiledGadget α 3).trace = 3 * α + 6 := by
  rw [compiledGadget_trace_formula]
  ring

end PallLean.Paper93.DeepMath.PathB

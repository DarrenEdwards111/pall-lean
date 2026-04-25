import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianPSDNonnegSymm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Positive definiteness of the compiled gadget (Path B)

The compiled gadget
`compiledGadget α n := α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n)`
is positive definite when `α > 0` and `n ≥ 1`.

The proof decomposes the gadget into two pieces:
  * `α • I` is `PosDef` for `α > 0` (positive multiple of the identity).
  * `L_{K_n}` is `PosSemidef` (Laplacian of a symmetric, non-negative
    adjacency matrix; the standard quadratic-form computation
    `vᵀLv = ½ ∑_{i,j} A_{ij} (v_i - v_j)²`).
A `PosDef` matrix plus a `PosSemidef` matrix is again `PosDef`, hence the
quadratic form `vᵀ(α • I + L) v = α‖v‖² + vᵀLv` is strictly positive on
nonzero vectors. This file packages that argument as a `Matrix.PosDef`
statement under the explicit hypotheses requested at the Path B layer.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

/-- The complete-graph adjacency matrix has non-negative real entries:
either `0` (on the diagonal) or `1` (off-diagonal). -/
lemma completeAdj_nonneg_pathB (n : ℕ) (i j : Fin n) : 0 ≤ completeAdj n i j := by
  unfold completeAdj
  by_cases h : i = j
  · simp [h]
  · simp [h]

/-- **Path B positive-definiteness of the compiled gadget.**

For `α > 0` and `n ≥ 1`, the compiled gadget
`compiledGadget α n = α • I + laplacian (completeAdj n)`
is positive definite as a real matrix on `Fin n`.

The proof factors through Mathlib's `Matrix.PosDef` API:
* `α • I` is `PosDef` since `α > 0` and the identity is `PosDef`
  (`Matrix.PosDef.one.smul`).
* `laplacian (completeAdj n)` is `PosSemidef` because `completeAdj n` is
  symmetric with non-negative entries
  (`laplacian_posSemidef_of_symm_nonneg`).
* `PosDef + PosSemidef` is `PosDef` (`Matrix.PosDef.add_posSemidef`).

The hypothesis `1 ≤ n` is not strictly required for the abstract
positive-definite conclusion (when `n = 0` the matrix is the empty
matrix, which is vacuously `PosDef`), but it is included in the
statement to match the Path B convention that the gadget acts on a
non-empty vertex set. -/
theorem compiledGadget_posDef (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    (compiledGadget α n).PosDef := by
  -- The hypothesis `hn : 1 ≤ n` is recorded for downstream callers; the
  -- `PosDef` argument itself does not depend on `n` being non-zero.
  let _ := hn
  unfold compiledGadget
  -- Step 1: `α • I` is `PosDef`.
  have h_smul_id : (α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    (Matrix.PosDef.one).smul hα
  -- Step 2: `L_{K_n}` is `PosSemidef`.
  have h_lap_psd : (laplacian (completeAdj n)).PosSemidef :=
    laplacian_posSemidef_of_symm_nonneg
      (completeAdj n) (completeAdj_symm n) (completeAdj_nonneg_pathB n)
  -- Step 3: `PosDef + PosSemidef = PosDef`.
  exact h_smul_id.add_posSemidef h_lap_psd

end PallLean.Paper93.DeepMath.PathB

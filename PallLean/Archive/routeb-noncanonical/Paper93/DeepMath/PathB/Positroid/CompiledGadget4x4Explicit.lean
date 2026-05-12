import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Explicit 4×4 compiled gadget

For `n = 4`, the §28.3 compiled gadget `compiledGadget α 4 = α • I + L_{K_4}`
has explicit structure:
  * diagonal entries `(α + 3)` (since `(n-1) = 3`),
  * off-diagonals `-1`.

This file provides the diagonal-explicit theorems specialised to `n = 4`,
together with the obvious general-`n` restatement and a couple of
elementary corollaries.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- The diagonal entries of `compiledGadget α 4` are `α + 3`. -/
theorem compiledGadget_4x4_diag (α : ℝ) (i : Fin 4) :
    compiledGadget α 4 i i = α + 3 := by
  rw [compiledGadget_diagonal]
  norm_num

/-- For any `n ≥ 2`, the diagonal entry of `compiledGadget α n` is `α + (n-1)`. -/
theorem compiledGadget_diag_general (α : ℝ) (n : ℕ) (i : Fin n) :
    compiledGadget α n i i = α + ((n : ℝ) - 1) :=
  compiledGadget_diagonal α n i

/-- For `α = 1` and `n = 4`, the diagonal entry is `4`. -/
theorem compiledGadget_4x4_diag_at_one (i : Fin 4) :
    compiledGadget 1 4 i i = 4 := by
  rw [compiledGadget_4x4_diag]
  norm_num

/-- For `n = 4` and `α > 0`, the diagonal entry strictly exceeds `3`. -/
theorem compiledGadget_4x4_diag_pos (α : ℝ) (hα : 0 < α) (i : Fin 4) :
    3 < compiledGadget α 4 i i := by
  rw [compiledGadget_4x4_diag]
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid

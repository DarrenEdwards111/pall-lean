import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Diagonal-entry specifics for the compiled gadget at `n = 4`

This file specialises the general diagonal/trace machinery for the
§28.3 compiled gadget `compiledGadget α n = α • I + L_{K_n}` to the
case `n = 4`, providing:

* `compiledGadget_4x4_diag_4` : every diagonal entry of
  `compiledGadget α 4` equals `α + 3` (i.e. `α + (4 - 1)`).
* `compiledGadget_4x4_trace` : the trace equals `4 * α + 12`
  (i.e. `n * α + n * (n - 1)` for `n = 4`).
* `compiledGadget_4x4_trace_at_one` : at `α = 1`, the trace evaluates
  to `16`.
* `compiledGadget_4x4_diag_sum` : the sum of diagonal entries
  `∑ i : Fin 4, compiledGadget α 4 i i` agrees with the trace
  `4 * α + 12`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For `n = 4`, every diagonal entry of `compiledGadget α 4` equals
`α + 3`.  This follows from the general diagonal formula
`compiledGadget α n i i = α + (n - 1)` evaluated at `n = 4`. -/
theorem compiledGadget_4x4_diag_4 (α : ℝ) (i : Fin 4) :
    compiledGadget α 4 i i = α + 3 := by
  rw [compiledGadget_diagonal]
  norm_num

/-- For `n = 4`, the trace of `compiledGadget α 4` equals `4 * α + 12`.
This follows from the general trace formula
`trace (compiledGadget α n) = n * α + n * (n - 1)` at `n = 4`. -/
theorem compiledGadget_4x4_trace (α : ℝ) :
    (compiledGadget α 4).trace = 4 * α + 12 := by
  rw [compiledGadget_trace_formula]
  ring

/-- Specialising the trace formula to `α = 1` and `n = 4` gives the
explicit value `(compiledGadget 1 4).trace = 16`. -/
theorem compiledGadget_4x4_trace_at_one :
    (compiledGadget 1 4).trace = 16 := by
  rw [compiledGadget_4x4_trace]
  norm_num

/-- For `n = 4`, the sum of diagonal entries of `compiledGadget α 4`
agrees with its trace, namely `4 * α + 12`.  Here we use the
definitional equality `Matrix.trace M = ∑ i, M i i`. -/
theorem compiledGadget_4x4_diag_sum (α : ℝ) :
    ∑ i : Fin 4, compiledGadget α 4 i i = 4 * α + 12 := by
  have : (compiledGadget α 4).trace = ∑ i : Fin 4, compiledGadget α 4 i i := rfl
  rw [← this]
  exact compiledGadget_4x4_trace α

end PallLean.Paper93.DeepMath.PathB.Positroid

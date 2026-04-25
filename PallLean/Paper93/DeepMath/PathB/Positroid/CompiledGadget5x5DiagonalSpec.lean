import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Diagonal-entry specifics for the compiled gadget at `n = 5`

This file specialises the general diagonal/trace machinery for the
§28.3 compiled gadget `compiledGadget α n = α • I + L_{K_n}` to the
case `n = 5`, providing:

* `compiledGadget_5x5_diag` : every diagonal entry of
  `compiledGadget α 5` equals `α + 4` (i.e. `α + (5 - 1)`).
* `compiledGadget_5x5_trace` : the trace equals `5 * α + 20`
  (i.e. `n * α + n * (n - 1)` for `n = 5`).
* `compiledGadget_5x5_trace_at_one` : at `α = 1`, the trace evaluates
  to `25`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For `n = 5`, every diagonal entry of `compiledGadget α 5` equals
`α + 4`.  This follows from the general diagonal formula
`compiledGadget α n i i = α + (n - 1)` evaluated at `n = 5`. -/
theorem compiledGadget_5x5_diag (α : ℝ) (i : Fin 5) :
    compiledGadget α 5 i i = α + 4 := by
  rw [compiledGadget_diagonal]
  norm_num

/-- For `n = 5`, the trace of `compiledGadget α 5` equals `5 * α + 20`.
This follows from the general trace formula
`trace (compiledGadget α n) = n * α + n * (n - 1)` at `n = 5`. -/
theorem compiledGadget_5x5_trace (α : ℝ) :
    (compiledGadget α 5).trace = 5 * α + 20 := by
  rw [compiledGadget_trace_formula]
  ring

/-- Specialising the trace formula to `α = 1` and `n = 5` gives the
explicit value `(compiledGadget 1 5).trace = 25`. -/
theorem compiledGadget_5x5_trace_at_one :
    (compiledGadget 1 5).trace = 25 := by
  rw [compiledGadget_5x5_trace]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

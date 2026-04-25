import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Diagonal-entry specifics for the compiled gadget at small `n`

This file specialises the general diagonal/trace machinery for the
§28.3 compiled gadget `compiledGadget α n = α • I + L_{K_n}` to the
cases `n ∈ {6, 7, 8}`, providing:

* `compiledGadget_6x6_diag` : every diagonal entry of
  `compiledGadget α 6` equals `α + 5` (i.e. `α + (6 - 1)`).
* `compiledGadget_7x7_diag` : every diagonal entry of
  `compiledGadget α 7` equals `α + 6` (i.e. `α + (7 - 1)`).
* `compiledGadget_8x8_diag` : every diagonal entry of
  `compiledGadget α 8` equals `α + 7` (i.e. `α + (8 - 1)`).
* `compiledGadget_6x6_trace` : the trace equals `6 * α + 30`
  (i.e. `n * α + n * (n - 1)` for `n = 6`).
* `compiledGadget_7x7_trace` : the trace equals `7 * α + 42`
  (i.e. `n * α + n * (n - 1)` for `n = 7`).
* `compiledGadget_8x8_trace` : the trace equals `8 * α + 56`
  (i.e. `n * α + n * (n - 1)` for `n = 8`).

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- compiledGadget α 6: diagonal = α + 5. -/
theorem compiledGadget_6x6_diag (α : ℝ) (i : Fin 6) :
    compiledGadget α 6 i i = α + 5 := by
  rw [compiledGadget_diagonal]
  norm_num

/-- compiledGadget α 7: diagonal = α + 6. -/
theorem compiledGadget_7x7_diag (α : ℝ) (i : Fin 7) :
    compiledGadget α 7 i i = α + 6 := by
  rw [compiledGadget_diagonal]
  norm_num

/-- compiledGadget α 8: diagonal = α + 7. -/
theorem compiledGadget_8x8_diag (α : ℝ) (i : Fin 8) :
    compiledGadget α 8 i i = α + 7 := by
  rw [compiledGadget_diagonal]
  norm_num

/-- compiledGadget α 6: trace = 6α + 30. -/
theorem compiledGadget_6x6_trace (α : ℝ) :
    (compiledGadget α 6).trace = 6 * α + 30 := by
  rw [compiledGadget_trace_formula]
  ring

/-- compiledGadget α 7: trace = 7α + 42. -/
theorem compiledGadget_7x7_trace (α : ℝ) :
    (compiledGadget α 7).trace = 7 * α + 42 := by
  rw [compiledGadget_trace_formula]
  ring

/-- compiledGadget α 8: trace = 8α + 56. -/
theorem compiledGadget_8x8_trace (α : ℝ) :
    (compiledGadget α 8).trace = 8 * α + 56 := by
  rw [compiledGadget_trace_formula]
  ring

end PallLean.Paper93.DeepMath.PathB.Positroid

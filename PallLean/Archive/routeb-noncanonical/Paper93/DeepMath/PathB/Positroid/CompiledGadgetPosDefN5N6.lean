import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum

/-!
# Explicit `PosDef`, determinant positivity, and determinant value witnesses
  for `compiledGadget 1 5` and `compiledGadget 1 6`

This file specialises the Path B positive--definiteness result
`compiledGadget_posDef` and the closed--form determinant identities
`compiledGadget_5x5_det` / `compiledGadget_6x6_det` to the gauge-distinguished
coupling `α = 1` at sizes `n ∈ {5, 6}`. We collect six witnesses:

* `compiledGadget_posDef_n5_at_one` — `(compiledGadget 1 5).PosDef`
  obtained from `compiledGadget_posDef 1 5` with `0 < 1` and `1 ≤ 5`.
* `compiledGadget_posDef_n6_at_one` — `(compiledGadget 1 6).PosDef`
  obtained from `compiledGadget_posDef 1 6` with `0 < 1` and `1 ≤ 6`.
* `compiledGadget_det_pos_n5_at_one` — `0 < (compiledGadget 1 5).det`
  via `Matrix.PosDef.det_pos`.
* `compiledGadget_det_pos_n6_at_one` — `0 < (compiledGadget 1 6).det`
  via `Matrix.PosDef.det_pos`.
* `compiledGadget_5x5_at_one_det_eq_1296` — the explicit value
  `(compiledGadget 1 5).det = 1296` from `compiledGadget_5x5_det` and
  `1 * (1 + 5)^4 = 1 * 6^4 = 1296`.
* `compiledGadget_6x6_at_one_det_eq_16807` — the explicit value
  `(compiledGadget 1 6).det = 16807` from `compiledGadget_6x6_det` and
  `1 * (1 + 6)^5 = 1 * 7^5 = 16807`.

Kernel--only: only `propext`, `Classical.choice`, `Quot.sound` are used.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-! ### Positive definiteness at `α = 1` for `n = 5, 6` -/

/-- **`compiledGadget 1 5` is `PosDef`.**

Specialising `compiledGadget_posDef` at `α = 1` (with `0 < 1` provided by
`one_pos`) and `n = 5` (with `1 ≤ 5` discharged by `norm_num`). -/
theorem compiledGadget_posDef_n5_at_one :
    (compiledGadget 1 5).PosDef :=
  compiledGadget_posDef 1 5 one_pos (by norm_num : (1 : ℕ) ≤ 5)

/-- **`compiledGadget 1 6` is `PosDef`.**

Specialising `compiledGadget_posDef` at `α = 1` (with `0 < 1` provided by
`one_pos`) and `n = 6` (with `1 ≤ 6` discharged by `norm_num`). -/
theorem compiledGadget_posDef_n6_at_one :
    (compiledGadget 1 6).PosDef :=
  compiledGadget_posDef 1 6 one_pos (by norm_num : (1 : ℕ) ≤ 6)

/-! ### Determinant positivity at `α = 1` via `Matrix.PosDef.det_pos` -/

/-- **The determinant of `compiledGadget 1 5` is strictly positive.**

Direct consequence of `Matrix.PosDef.det_pos` applied to the witness
`compiledGadget_posDef_n5_at_one`. -/
theorem compiledGadget_det_pos_n5_at_one :
    0 < (compiledGadget 1 5).det :=
  Matrix.PosDef.det_pos compiledGadget_posDef_n5_at_one

/-- **The determinant of `compiledGadget 1 6` is strictly positive.**

Direct consequence of `Matrix.PosDef.det_pos` applied to the witness
`compiledGadget_posDef_n6_at_one`. -/
theorem compiledGadget_det_pos_n6_at_one :
    0 < (compiledGadget 1 6).det :=
  Matrix.PosDef.det_pos compiledGadget_posDef_n6_at_one

/-! ### Explicit numerical determinant values at `α = 1` -/

/-- **Explicit value of the 5×5 compiled gadget determinant at `α = 1`.**

By the closed--form `compiledGadget_5x5_det`, we have
`(compiledGadget α 5).det = α * (α + 5)^4`. Specialising at `α = 1` gives
`1 * 6^4 = 1296`, which `norm_num` evaluates. -/
theorem compiledGadget_5x5_at_one_det_eq_1296 :
    (compiledGadget 1 5).det = 1296 := by
  rw [compiledGadget_5x5_det]
  norm_num

/-- **Explicit value of the 6×6 compiled gadget determinant at `α = 1`.**

By the closed--form `compiledGadget_6x6_det`, we have
`(compiledGadget α 6).det = α * (α + 6)^5`. Specialising at `α = 1` gives
`1 * 7^5 = 16807`, which `norm_num` evaluates. -/
theorem compiledGadget_6x6_at_one_det_eq_16807 :
    (compiledGadget 1 6).det = 16807 := by
  rw [compiledGadget_6x6_det]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

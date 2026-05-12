import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Compiled gadget PosDef / det / rank witnesses at large `n`

This file extends the `n = 15..20` instance suite of
`CompiledGadgetDetPosN15ToN20.lean` and `CompiledGadgetRankN15ToN20.lean`
to the larger sizes `n ∈ {25, 30, 50, 100}`. For each such `n` we record
three kernel--only consequences of the generic positive--definiteness
theorem `compiledGadget_posDef` (proved in
`PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef`):

* the compiled gadget is positive definite at `α > 0`,
* its determinant is strictly positive (via `Matrix.PosDef.det_pos`),
* its rank equals `n` (via `compiledGadget_rank_full`).

Each instance is obtained by specialising the generic statements with
the numeric witness `(by norm_num : 1 ≤ n)`. The file is purely a
specialisation layer: no new mathematical content is introduced, and no
`sorry` is required.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-! ### `n = 25` -/

theorem compiledGadget_posDef_n25 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 25).PosDef :=
  compiledGadget_posDef α 25 hα (by norm_num : (1 : ℕ) ≤ 25)

theorem compiledGadget_det_pos_n25 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 25).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef_n25 α hα)

theorem compiledGadget_rank_n25 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 25).rank = 25 :=
  compiledGadget_rank_full α 25 hα (by norm_num : (1 : ℕ) ≤ 25)

/-! ### `n = 30` -/

theorem compiledGadget_posDef_n30 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 30).PosDef :=
  compiledGadget_posDef α 30 hα (by norm_num : (1 : ℕ) ≤ 30)

theorem compiledGadget_det_pos_n30 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 30).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef_n30 α hα)

theorem compiledGadget_rank_n30 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 30).rank = 30 :=
  compiledGadget_rank_full α 30 hα (by norm_num : (1 : ℕ) ≤ 30)

/-! ### `n = 50` -/

theorem compiledGadget_posDef_n50 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 50).PosDef :=
  compiledGadget_posDef α 50 hα (by norm_num : (1 : ℕ) ≤ 50)

theorem compiledGadget_det_pos_n50 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 50).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef_n50 α hα)

theorem compiledGadget_rank_n50 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 50).rank = 50 :=
  compiledGadget_rank_full α 50 hα (by norm_num : (1 : ℕ) ≤ 50)

/-! ### `n = 100` -/

theorem compiledGadget_posDef_n100 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 100).PosDef :=
  compiledGadget_posDef α 100 hα (by norm_num : (1 : ℕ) ≤ 100)

theorem compiledGadget_det_pos_n100 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 100).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef_n100 α hα)

theorem compiledGadget_rank_n100 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 100).rank = 100 :=
  compiledGadget_rank_full α 100 hα (by norm_num : (1 : ℕ) ≤ 100)

end PallLean.Paper93.DeepMath.PathB.Positroid

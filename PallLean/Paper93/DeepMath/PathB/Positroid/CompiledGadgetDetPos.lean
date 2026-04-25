import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The determinant of compiledGadget α n is positive for α > 0 and n ≥ 1
    (via PosDef ⇒ det > 0). -/
theorem compiledGadget_det_pos (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    0 < (compiledGadget α n).det := by
  exact Matrix.PosDef.det_pos (compiledGadget_posDef α n hα hn)

/-- For α > 0 and n ≥ 1, the determinant is positive. -/
theorem compiledGadget_det_pos_n2 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 2).det :=
  compiledGadget_det_pos α 2 hα (by norm_num)

theorem compiledGadget_det_pos_n3 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 3).det :=
  compiledGadget_det_pos α 3 hα (by norm_num)

theorem compiledGadget_det_pos_n4 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 4).det :=
  compiledGadget_det_pos α 4 hα (by norm_num)

theorem compiledGadget_det_pos_n5 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 5).det :=
  compiledGadget_det_pos α 5 hα (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid

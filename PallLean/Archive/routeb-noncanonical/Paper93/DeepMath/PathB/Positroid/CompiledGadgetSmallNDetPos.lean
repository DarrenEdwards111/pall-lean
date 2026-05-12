import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_6x6_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 6).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 6 hα (by norm_num))

theorem compiledGadget_7x7_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 7).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 7 hα (by norm_num))

theorem compiledGadget_8x8_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 8).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 8 hα (by norm_num))

theorem compiledGadget_general_det_pos (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    0 < (compiledGadget α n).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α n hα hn)

end PallLean.Paper93.DeepMath.PathB.Positroid

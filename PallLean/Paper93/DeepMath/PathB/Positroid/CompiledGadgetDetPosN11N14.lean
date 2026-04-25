import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_11x11_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 11).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 11 hα (by norm_num))

theorem compiledGadget_12x12_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 12).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 12 hα (by norm_num))

theorem compiledGadget_13x13_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 13).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 13 hα (by norm_num))

theorem compiledGadget_14x14_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 14).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 14 hα (by norm_num))

end PallLean.Paper93.DeepMath.PathB.Positroid

import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_det_pos_n15 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 15).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 15 hα (by norm_num))

theorem compiledGadget_det_pos_n16 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 16).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 16 hα (by norm_num))

theorem compiledGadget_det_pos_n17 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 17).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 17 hα (by norm_num))

theorem compiledGadget_det_pos_n18 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 18).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 18 hα (by norm_num))

theorem compiledGadget_det_pos_n19 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 19).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 19 hα (by norm_num))

theorem compiledGadget_det_pos_n20 (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 20).det :=
  Matrix.PosDef.det_pos (compiledGadget_posDef α 20 hα (by norm_num))

end PallLean.Paper93.DeepMath.PathB.Positroid

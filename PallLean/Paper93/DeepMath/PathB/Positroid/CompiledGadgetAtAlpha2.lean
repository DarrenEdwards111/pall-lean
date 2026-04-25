import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_2_2_det : (compiledGadget 2 2).det = 8 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_2_3_det : (compiledGadget 2 3).det = 50 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_2_4_det : (compiledGadget 2 4).det = 432 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_2_2_det_pos : 0 < (compiledGadget 2 2).det := by
  rw [compiledGadget_2_2_det]; norm_num

theorem compiledGadget_2_3_det_pos : 0 < (compiledGadget 2 3).det := by
  rw [compiledGadget_2_3_det]; norm_num

theorem compiledGadget_2_4_det_pos : 0 < (compiledGadget 2 4).det := by
  rw [compiledGadget_2_4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

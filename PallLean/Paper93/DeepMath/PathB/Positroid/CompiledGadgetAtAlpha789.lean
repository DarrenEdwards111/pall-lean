import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_7_2_det : (compiledGadget 7 2).det = 63 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_7_3_det : (compiledGadget 7 3).det = 700 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_7_4_det : (compiledGadget 7 4).det = 9317 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_8_2_det : (compiledGadget 8 2).det = 80 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_8_3_det : (compiledGadget 8 3).det = 968 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_8_4_det : (compiledGadget 8 4).det = 13824 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_9_2_det : (compiledGadget 9 2).det = 99 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_9_3_det : (compiledGadget 9 3).det = 1296 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_9_4_det : (compiledGadget 9 4).det = 19773 := by
  rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

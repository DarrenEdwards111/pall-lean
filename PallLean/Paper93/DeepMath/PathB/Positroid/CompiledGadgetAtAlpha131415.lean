import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

-- α=13: α(α+2)=195, α(α+3)²=3328, α(α+4)³=63869
theorem compiledGadget_13_2_det : (compiledGadget 13 2).det = 195 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_13_3_det : (compiledGadget 13 3).det = 3328 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_13_4_det : (compiledGadget 13 4).det = 63869 := by
  rw [compiledGadget_4x4_det]; norm_num

-- α=14: α(α+2)=224, α(α+3)²=4046, α(α+4)³=81648
theorem compiledGadget_14_2_det : (compiledGadget 14 2).det = 224 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_14_3_det : (compiledGadget 14 3).det = 4046 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_14_4_det : (compiledGadget 14 4).det = 81648 := by
  rw [compiledGadget_4x4_det]; norm_num

-- α=15: α(α+2)=255, α(α+3)²=4860, α(α+4)³=102885
theorem compiledGadget_15_2_det : (compiledGadget 15 2).det = 255 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_15_3_det : (compiledGadget 15 3).det = 4860 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_15_4_det : (compiledGadget 15 4).det = 102885 := by
  rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

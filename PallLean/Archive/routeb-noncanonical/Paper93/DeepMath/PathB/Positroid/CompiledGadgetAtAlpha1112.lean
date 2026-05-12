import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

-- α=11: α(α+2)=143, α(α+3)²=2156, α(α+4)³=37125
theorem compiledGadget_11_2_det : (compiledGadget 11 2).det = 143 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_11_3_det : (compiledGadget 11 3).det = 2156 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_11_4_det : (compiledGadget 11 4).det = 37125 := by
  rw [compiledGadget_4x4_det]; norm_num

-- α=12: α(α+2)=168, α(α+3)²=2700, α(α+4)³=49152
theorem compiledGadget_12_2_det : (compiledGadget 12 2).det = 168 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_12_3_det : (compiledGadget 12 3).det = 2700 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_12_4_det : (compiledGadget 12 4).det = 49152 := by
  rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

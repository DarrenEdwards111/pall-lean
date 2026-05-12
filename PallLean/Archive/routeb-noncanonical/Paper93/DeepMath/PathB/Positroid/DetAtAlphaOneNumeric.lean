import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem det_at_alpha_one_pattern_n2 : (compiledGadget 1 2).det = 1 * (1 + 2)^1 := by
  rw [compiledGadget_2x2_det]; ring

theorem det_at_alpha_one_pattern_n3 : (compiledGadget 1 3).det = 1 * (1 + 3)^2 := by
  rw [compiledGadget_3x3_det]

theorem det_at_alpha_one_pattern_n4 : (compiledGadget 1 4).det = 1 * (1 + 4)^3 := by
  rw [compiledGadget_4x4_det]

theorem det_at_alpha_one_3 : (compiledGadget 1 2).det = 3 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem det_at_alpha_one_16 : (compiledGadget 1 3).det = 16 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem det_at_alpha_one_125 : (compiledGadget 1 4).det = 125 := by
  rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

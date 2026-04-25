import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_4_2_det : (compiledGadget 4 2).det = 24 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_4_3_det : (compiledGadget 4 3).det = 196 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_4_4_det : (compiledGadget 4 4).det = 2048 := by
  rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_10_2_det : (compiledGadget 10 2).det = 120 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_10_3_det : (compiledGadget 10 3).det = 1690 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_10_4_det : (compiledGadget 10 4).det = 27440 := by
  rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

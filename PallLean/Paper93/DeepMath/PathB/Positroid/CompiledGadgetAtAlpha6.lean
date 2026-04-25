import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_6_2_det : (compiledGadget 6 2).det = 48 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_6_3_det : (compiledGadget 6 3).det = 486 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_6_4_det : (compiledGadget 6 4).det = 6000 := by
  rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

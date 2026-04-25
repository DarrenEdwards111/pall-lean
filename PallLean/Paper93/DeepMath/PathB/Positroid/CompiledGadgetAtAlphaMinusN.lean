import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_neg2_2_det : (compiledGadget (-2) 2).det = 0 := by
  rw [compiledGadget_2x2_det]; ring

theorem compiledGadget_neg3_3_det : (compiledGadget (-3) 3).det = 0 := by
  rw [compiledGadget_3x3_det]; ring

theorem compiledGadget_neg4_4_det : (compiledGadget (-4) 4).det = 0 := by
  rw [compiledGadget_4x4_det]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid

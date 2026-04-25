import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem det_specific_values_bundle :
    -- α=1
    (compiledGadget 1 2).det = 3 ∧
    (compiledGadget 1 3).det = 16 ∧
    (compiledGadget 1 4).det = 125 ∧
    -- α=2
    (compiledGadget 2 2).det = 8 ∧
    (compiledGadget 2 3).det = 50 ∧
    (compiledGadget 2 4).det = 432 ∧
    -- α=3
    (compiledGadget 3 2).det = 15 ∧
    (compiledGadget 3 3).det = 108 ∧
    (compiledGadget 3 4).det = 1029 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [compiledGadget_2x2_det]; norm_num
  · rw [compiledGadget_3x3_det]; norm_num
  · rw [compiledGadget_4x4_det]; norm_num
  · rw [compiledGadget_2x2_det]; norm_num
  · rw [compiledGadget_3x3_det]; norm_num
  · rw [compiledGadget_4x4_det]; norm_num
  · rw [compiledGadget_2x2_det]; norm_num
  · rw [compiledGadget_3x3_det]; norm_num
  · rw [compiledGadget_4x4_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid

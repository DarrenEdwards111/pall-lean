import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem det_bundle_r66 :
    (compiledGadget 4 2).det = 24 ∧
    (compiledGadget 4 3).det = 196 ∧
    (compiledGadget 4 4).det = 2048 ∧
    (compiledGadget 5 2).det = 35 ∧
    (compiledGadget 5 3).det = 320 ∧
    (compiledGadget 5 4).det = 3645 ∧
    (compiledGadget 6 2).det = 48 ∧
    (compiledGadget 6 3).det = 486 ∧
    (compiledGadget 6 4).det = 6000 ∧
    (compiledGadget 10 2).det = 120 ∧
    (compiledGadget 10 3).det = 1690 ∧
    (compiledGadget 10 4).det = 27440 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [compiledGadget_2x2_det]; norm_num
  · rw [compiledGadget_3x3_det]; norm_num
  · rw [compiledGadget_4x4_det]; norm_num
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

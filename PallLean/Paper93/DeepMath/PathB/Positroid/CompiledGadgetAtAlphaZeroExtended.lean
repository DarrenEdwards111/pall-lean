import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetAtAlphaZero
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- At α = 0, det vanishes for n=2,3,4. Bundled. -/
theorem compiledGadget_alpha_zero_det_zero_bundle :
    (compiledGadget 0 2).det = 0 ∧
    (compiledGadget 0 3).det = 0 ∧
    (compiledGadget 0 4).det = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [compiledGadget_2x2_det]; ring
  · rw [compiledGadget_3x3_det]; ring
  · rw [compiledGadget_4x4_det]; ring

/-- At α = -n, det vanishes for n=2,3,4. -/
theorem compiledGadget_alpha_neg_n_det_zero_bundle :
    (compiledGadget (-2) 2).det = 0 ∧
    (compiledGadget (-3) 3).det = 0 ∧
    (compiledGadget (-4) 4).det = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [compiledGadget_2x2_det]; ring
  · rw [compiledGadget_3x3_det]; ring
  · rw [compiledGadget_4x4_det]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid

import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Determinant values at α=1..12 for n=2. -/
theorem det_at_alpha_n2_bundle :
    (compiledGadget 1 2).det = 3 ∧
    (compiledGadget 2 2).det = 8 ∧
    (compiledGadget 3 2).det = 15 ∧
    (compiledGadget 4 2).det = 24 ∧
    (compiledGadget 5 2).det = 35 ∧
    (compiledGadget 6 2).det = 48 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (rw [compiledGadget_2x2_det]; norm_num)

/-- Determinant values at α=1..6 for n=3. -/
theorem det_at_alpha_n3_bundle :
    (compiledGadget 1 3).det = 16 ∧
    (compiledGadget 2 3).det = 50 ∧
    (compiledGadget 3 3).det = 108 ∧
    (compiledGadget 4 3).det = 196 ∧
    (compiledGadget 5 3).det = 320 ∧
    (compiledGadget 6 3).det = 486 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (rw [compiledGadget_3x3_det]; norm_num)

/-- Determinant values at α=1..6 for n=4. -/
theorem det_at_alpha_n4_bundle :
    (compiledGadget 1 4).det = 125 ∧
    (compiledGadget 2 4).det = 432 ∧
    (compiledGadget 3 4).det = 1029 ∧
    (compiledGadget 4 4).det = 2048 ∧
    (compiledGadget 5 4).det = 3645 ∧
    (compiledGadget 6 4).det = 6000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (rw [compiledGadget_4x4_det]; norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid

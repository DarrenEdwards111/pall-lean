import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Closed-form det formulas for compiledGadget at n=1,2,3,4: bundled. -/
theorem compiledGadget_det_formula_n_le_4 :
    (∀ α : ℝ, (compiledGadget α 1).det = α) ∧
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact compiledGadget_1x1_det
  · exact compiledGadget_2x2_det
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det

/-- The pattern α(α+n)^(n-1) holds for n=1..4: existence form. -/
theorem compiledGadget_det_pattern_witnessed :
    (∀ α : ℝ, (compiledGadget α 1).det = α * (α + 1)^0) ∧
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)^1) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α
    rw [compiledGadget_1x1_det]; ring
  · intro α
    rw [compiledGadget_2x2_det]; ring
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det

end PallLean.Paper93.DeepMath.PathB.Positroid

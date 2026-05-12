import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Closed-form det formula at n=1..4 extracted as explicit α-formulas. -/
theorem closed_form_det_n1_to_n4 :
    (∀ α : ℝ, (compiledGadget α 1).det = α) ∧
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact compiledGadget_1x1_det
  · exact compiledGadget_2x2_det
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det

/-- The conjectured pattern α(α+n)^(n-1) confirmed at n=1, 2, 3, 4. -/
theorem closed_form_pattern_confirmed :
    (∀ α : ℝ, (compiledGadget α 1).det = α * (α + 1)^0) ∧
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)^1) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α; rw [compiledGadget_1x1_det]; ring
  · intro α; rw [compiledGadget_2x2_det]; ring
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det

end PallLean.Paper93.DeepMath.PathB.Positroid

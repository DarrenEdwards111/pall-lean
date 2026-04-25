import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem round_65_deep_progress :
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) ∧
    (∃ A : Matrix (Fin 11) (Fin 11) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 11) (Fin 11) ℝ)) ∧
    (∃ A : Matrix (Fin 12) (Fin 12) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 12) (Fin 12) ℝ)) ∧
    (∃ A : Matrix (Fin 13) (Fin 13) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 13) (Fin 13) ℝ)) ∧
    (∃ A : Matrix (Fin 14) (Fin 14) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 14) (Fin 14) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · exact compiledGadget_2x2_det
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det
  · exact ⟨compiledGadget 1 11, compiledGadget_posDef 1 11 one_pos (by norm_num),
           compiledGadget_ne_identity 1 11 (by norm_num)⟩
  · exact ⟨compiledGadget 1 12, compiledGadget_posDef 1 12 one_pos (by norm_num),
           compiledGadget_ne_identity 1 12 (by norm_num)⟩
  · exact ⟨compiledGadget 1 13, compiledGadget_posDef 1 13 one_pos (by norm_num),
           compiledGadget_ne_identity 1 13 (by norm_num)⟩
  · exact ⟨compiledGadget 1 14, compiledGadget_posDef 1 14 one_pos (by norm_num),
           compiledGadget_ne_identity 1 14 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

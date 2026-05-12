import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem nonidentity_posDef_bundle_n_2_to_12 :
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    (∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    (∃ A : Matrix (Fin 5) (Fin 5) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)) ∧
    (∃ A : Matrix (Fin 6) (Fin 6) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)) ∧
    (∃ A : Matrix (Fin 7) (Fin 7) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ)) ∧
    (∃ A : Matrix (Fin 8) (Fin 8) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ)) ∧
    (∃ A : Matrix (Fin 9) (Fin 9) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 9) (Fin 9) ℝ)) ∧
    (∃ A : Matrix (Fin 10) (Fin 10) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 10) (Fin 10) ℝ)) ∧
    (∃ A : Matrix (Fin 11) (Fin 11) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 11) (Fin 11) ℝ)) ∧
    (∃ A : Matrix (Fin 12) (Fin 12) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 12) (Fin 12) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨compiledGadget 1 2, compiledGadget_posDef 1 2 one_pos (by norm_num), compiledGadget_ne_identity 1 2 (by norm_num)⟩
  · exact ⟨compiledGadget 1 3, compiledGadget_posDef 1 3 one_pos (by norm_num), compiledGadget_ne_identity 1 3 (by norm_num)⟩
  · exact ⟨compiledGadget 1 4, compiledGadget_posDef 1 4 one_pos (by norm_num), compiledGadget_ne_identity 1 4 (by norm_num)⟩
  · exact ⟨compiledGadget 1 5, compiledGadget_posDef 1 5 one_pos (by norm_num), compiledGadget_ne_identity 1 5 (by norm_num)⟩
  · exact ⟨compiledGadget 1 6, compiledGadget_posDef 1 6 one_pos (by norm_num), compiledGadget_ne_identity 1 6 (by norm_num)⟩
  · exact ⟨compiledGadget 1 7, compiledGadget_posDef 1 7 one_pos (by norm_num), compiledGadget_ne_identity 1 7 (by norm_num)⟩
  · exact ⟨compiledGadget 1 8, compiledGadget_posDef 1 8 one_pos (by norm_num), compiledGadget_ne_identity 1 8 (by norm_num)⟩
  · exact ⟨compiledGadget 1 9, compiledGadget_posDef 1 9 one_pos (by norm_num), compiledGadget_ne_identity 1 9 (by norm_num)⟩
  · exact ⟨compiledGadget 1 10, compiledGadget_posDef 1 10 one_pos (by norm_num), compiledGadget_ne_identity 1 10 (by norm_num)⟩
  · exact ⟨compiledGadget 1 11, compiledGadget_posDef 1 11 one_pos (by norm_num), compiledGadget_ne_identity 1 11 (by norm_num)⟩
  · exact ⟨compiledGadget 1 12, compiledGadget_posDef 1 12 one_pos (by norm_num), compiledGadget_ne_identity 1 12 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

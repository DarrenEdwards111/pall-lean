import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem exists_nonidentity_posDef_n15 :
    ∃ A : Matrix (Fin 15) (Fin 15) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 15) (Fin 15) ℝ) :=
  ⟨compiledGadget 1 15, compiledGadget_posDef 1 15 one_pos (by norm_num),
   compiledGadget_ne_identity 1 15 (by norm_num)⟩

theorem exists_nonidentity_posDef_n16 :
    ∃ A : Matrix (Fin 16) (Fin 16) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 16) (Fin 16) ℝ) :=
  ⟨compiledGadget 1 16, compiledGadget_posDef 1 16 one_pos (by norm_num),
   compiledGadget_ne_identity 1 16 (by norm_num)⟩

theorem exists_nonidentity_posDef_n17 :
    ∃ A : Matrix (Fin 17) (Fin 17) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 17) (Fin 17) ℝ) :=
  ⟨compiledGadget 1 17, compiledGadget_posDef 1 17 one_pos (by norm_num),
   compiledGadget_ne_identity 1 17 (by norm_num)⟩

theorem exists_nonidentity_posDef_n18 :
    ∃ A : Matrix (Fin 18) (Fin 18) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 18) (Fin 18) ℝ) :=
  ⟨compiledGadget 1 18, compiledGadget_posDef 1 18 one_pos (by norm_num),
   compiledGadget_ne_identity 1 18 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

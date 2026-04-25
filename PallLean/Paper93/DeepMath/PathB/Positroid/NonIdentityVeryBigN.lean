import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem exists_nonidentity_posDef_n25 :
    ∃ A : Matrix (Fin 25) (Fin 25) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 25) (Fin 25) ℝ) :=
  ⟨compiledGadget 1 25, compiledGadget_posDef 1 25 one_pos (by norm_num),
   compiledGadget_ne_identity 1 25 (by norm_num)⟩

theorem exists_nonidentity_posDef_n30 :
    ∃ A : Matrix (Fin 30) (Fin 30) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 30) (Fin 30) ℝ) :=
  ⟨compiledGadget 1 30, compiledGadget_posDef 1 30 one_pos (by norm_num),
   compiledGadget_ne_identity 1 30 (by norm_num)⟩

theorem exists_nonidentity_posDef_n50 :
    ∃ A : Matrix (Fin 50) (Fin 50) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 50) (Fin 50) ℝ) :=
  ⟨compiledGadget 1 50, compiledGadget_posDef 1 50 one_pos (by norm_num),
   compiledGadget_ne_identity 1 50 (by norm_num)⟩

theorem exists_nonidentity_posDef_n100 :
    ∃ A : Matrix (Fin 100) (Fin 100) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 100) (Fin 100) ℝ) :=
  ⟨compiledGadget 1 100, compiledGadget_posDef 1 100 one_pos (by norm_num),
   compiledGadget_ne_identity 1 100 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

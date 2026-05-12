import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem exists_nonidentity_posDef_n19 :
    ∃ A : Matrix (Fin 19) (Fin 19) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 19) (Fin 19) ℝ) :=
  ⟨compiledGadget 1 19, compiledGadget_posDef 1 19 one_pos (by norm_num),
   compiledGadget_ne_identity 1 19 (by norm_num)⟩

theorem exists_nonidentity_posDef_n20 :
    ∃ A : Matrix (Fin 20) (Fin 20) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 20) (Fin 20) ℝ) :=
  ⟨compiledGadget 1 20, compiledGadget_posDef 1 20 one_pos (by norm_num),
   compiledGadget_ne_identity 1 20 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

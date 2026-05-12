import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem exists_nonidentity_posDef_n13 :
    ∃ A : Matrix (Fin 13) (Fin 13) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 13) (Fin 13) ℝ) :=
  ⟨compiledGadget 1 13, compiledGadget_posDef 1 13 one_pos (by norm_num),
   compiledGadget_ne_identity 1 13 (by norm_num)⟩

theorem exists_nonidentity_posDef_n14 :
    ∃ A : Matrix (Fin 14) (Fin 14) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 14) (Fin 14) ℝ) :=
  ⟨compiledGadget 1 14, compiledGadget_posDef 1 14 one_pos (by norm_num),
   compiledGadget_ne_identity 1 14 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

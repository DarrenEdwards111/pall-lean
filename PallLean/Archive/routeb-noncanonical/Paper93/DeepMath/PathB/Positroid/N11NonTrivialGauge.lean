import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_11x11_alpha_one_posDef_nonidentity :
    (compiledGadget 1 11).PosDef ∧
    compiledGadget 1 11 ≠ (1 : Matrix (Fin 11) (Fin 11) ℝ) :=
  ⟨compiledGadget_posDef 1 11 one_pos (by norm_num),
   compiledGadget_ne_identity 1 11 (by norm_num)⟩

theorem exists_nonidentity_posDef_n11 :
    ∃ A : Matrix (Fin 11) (Fin 11) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 11) (Fin 11) ℝ) :=
  ⟨compiledGadget 1 11, compiledGadget_posDef 1 11 one_pos (by norm_num),
   compiledGadget_ne_identity 1 11 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

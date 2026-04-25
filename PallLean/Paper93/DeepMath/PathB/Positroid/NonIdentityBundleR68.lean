import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Universal non-identity PosDef witness for n ≥ 2. -/
theorem exists_nonidentity_posDef_general (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨compiledGadget 1 n, compiledGadget_posDef 1 n one_pos (by omega),
   compiledGadget_ne_identity 1 n hn⟩

theorem exists_nonidentity_posDef_n2_to_n20 :
    ∀ n : ℕ, 2 ≤ n → n ≤ 20 →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intros n hn _
  exact exists_nonidentity_posDef_general n hn

end PallLean.Paper93.DeepMath.PathB.Positroid

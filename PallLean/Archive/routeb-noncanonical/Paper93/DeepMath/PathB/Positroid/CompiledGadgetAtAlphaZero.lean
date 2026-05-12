import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_0_2_det : (compiledGadget 0 2).det = 0 := by
  rw [compiledGadget_2x2_det]; ring

theorem compiledGadget_0_3_det : (compiledGadget 0 3).det = 0 := by
  rw [compiledGadget_3x3_det]; ring

theorem compiledGadget_0_4_det : (compiledGadget 0 4).det = 0 := by
  rw [compiledGadget_4x4_det]; ring

theorem compiledGadget_0_n_singular (n : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 4) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A = compiledGadget 0 n ∧ A.det = 0 := by
  rcases hn with h | h | h
  · subst h; exact ⟨compiledGadget 0 2, rfl, compiledGadget_0_2_det⟩
  · subst h; exact ⟨compiledGadget 0 3, rfl, compiledGadget_0_3_det⟩
  · subst h; exact ⟨compiledGadget 0 4, rfl, compiledGadget_0_4_det⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

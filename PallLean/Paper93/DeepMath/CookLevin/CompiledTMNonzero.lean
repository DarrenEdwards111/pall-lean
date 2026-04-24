import PallLean.Paper93.DeepMath.CookLevin.CompiledTM
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetNonzero

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- The compiled TM matrix is nonzero for α > 0 and tableau size ≥ 2. -/
theorem compiledTMMatrix_ne_zero
    (numStates numSymbols numTimesteps : ℕ) (α : ℝ)
    (hα : 0 < α)
    (hcard : 2 ≤ Fintype.card (TableauIndex numStates numSymbols numTimesteps)) :
    compiledTMMatrix numStates numSymbols numTimesteps α ≠ 0 := by
  unfold compiledTMMatrix
  -- compiledTMMatrix = (cookLevinGadget α k).submatrix e e where k = card and e is the Equiv.
  -- If cookLevinGadget α k ≠ 0, then the submatrix along a bijection is also ≠ 0.
  -- Since e is a bijection (Equiv), submatrix preserves nonzero-ness.
  intro h
  apply cookLevinGadget_ne_zero α _ hα hcard
  -- From h : (cookLevinGadget α k).submatrix e e = 0, deduce cookLevinGadget α k = 0.
  ext i j
  have hij :
      (cookLevinGadget α _).submatrix (Fintype.equivFin _) (Fintype.equivFin _)
          ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm j)
        = (0 :
            Matrix (TableauIndex numStates numSymbols numTimesteps)
                   (TableauIndex numStates numSymbols numTimesteps) ℝ)
          ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm j) := by
    rw [h]
  simp [Matrix.submatrix_apply, Equiv.apply_symm_apply] at hij
  simpa using hij

end PallLean.Paper93.DeepMath.CookLevin

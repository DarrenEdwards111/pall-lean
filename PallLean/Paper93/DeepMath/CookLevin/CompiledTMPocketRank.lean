import PallLean.Paper93.DeepMath.CookLevin.CompiledTM
import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetNonzero
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- The compiled TM matrix's rank equals the cookLevinGadget's rank (via re-indexing).

The compiled TM matrix is defined as
`(cookLevinGadget α k).submatrix e e` where `e : TableauIndex ≃ Fin k` is
`Fintype.equivFin _`. Since `e` is an `Equiv`, `Matrix.rank_submatrix` applies
and the rank is preserved. -/
theorem compiledTMMatrix_rank_eq
    (numStates numSymbols numTimesteps : ℕ) (α : ℝ) :
    (compiledTMMatrix numStates numSymbols numTimesteps α).rank
      = (cookLevinGadget α (Fintype.card (TableauIndex numStates numSymbols numTimesteps))).rank := by
  unfold compiledTMMatrix
  exact Matrix.rank_submatrix
    (cookLevinGadget α (Fintype.card (TableauIndex numStates numSymbols numTimesteps)))
    (Fintype.equivFin _) (Fintype.equivFin _)

end PallLean.Paper93.DeepMath.CookLevin

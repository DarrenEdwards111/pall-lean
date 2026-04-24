import PallLean.Paper93.DeepMath.CookLevin.CompiledTMNonzero
import PallLean.Paper93.DeepMath.GadgetRank.RankPosOfNe

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- Rank lower bound for the compiled Cook-Levin tableau matrix: for `α > 0`
    and at least two tableau cells, the compiled TM matrix has rank at least
    `1`. This composes `compiledTMMatrix_ne_zero` with `rank_pos_of_ne_zero`
    via the `Fin`-reindexing used in the definition of `compiledTMMatrix`. -/
theorem compiledTMMatrix_rank_pos
    (numStates numSymbols numTimesteps : ℕ) (α : ℝ)
    (hα : 0 < α)
    (hcard : 2 ≤ Fintype.card (TableauIndex numStates numSymbols numTimesteps)) :
    1 ≤ (compiledTMMatrix numStates numSymbols numTimesteps α).rank := by
  -- The compiled TM matrix is nonzero.
  have hne : compiledTMMatrix numStates numSymbols numTimesteps α ≠ 0 :=
    compiledTMMatrix_ne_zero numStates numSymbols numTimesteps α hα hcard
  -- `compiledTMMatrix` is `(cookLevinGadget α k).submatrix e e` where
  -- `e : TableauIndex ≃ Fin k` is `Fintype.equivFin _`.
  -- Reindex via `e.symm` on both sides to land on a `Fin`-indexed matrix,
  -- whose rank equals the rank of `compiledTMMatrix` and which is nonzero
  -- iff `compiledTMMatrix` is.
  set k := Fintype.card (TableauIndex numStates numSymbols numTimesteps) with hk
  set e : TableauIndex numStates numSymbols numTimesteps ≃ Fin k :=
    Fintype.equivFin _ with he
  -- Define the `Fin`-reindexed matrix.
  set M' : Matrix (Fin k) (Fin k) ℝ :=
    (compiledTMMatrix numStates numSymbols numTimesteps α).submatrix e.symm e.symm
    with hM'
  -- Rank equality via `rank_submatrix` (the submatrix along an `Equiv`
  -- preserves rank).
  have hrank :
      M'.rank = (compiledTMMatrix numStates numSymbols numTimesteps α).rank := by
    simp [hM',
      Matrix.rank_submatrix
        (compiledTMMatrix numStates numSymbols numTimesteps α) e.symm e.symm]
  -- Nonzero transfers: if `M' = 0`, then applying `Matrix.submatrix` with `e`
  -- on both sides recovers `compiledTMMatrix = 0`, contradicting `hne`.
  have hne' : M' ≠ 0 := by
    intro h
    apply hne
    ext i j
    have hij :
        M'.submatrix e e i j = (0 : Matrix (Fin k) (Fin k) ℝ).submatrix e e i j := by
      rw [h]
    -- `M'.submatrix e e = compiledTMMatrix` since
    -- `((A.submatrix e.symm e.symm).submatrix e e) i j = A i j`.
    simpa [hM', Matrix.submatrix_apply, Equiv.symm_apply_apply] using hij
  -- Apply the `Fin`-indexed rank-positivity lemma.
  have hM'rank : 1 ≤ M'.rank := rank_pos_of_ne_zero M' hne'
  -- Transport along the rank equality.
  calc
    1 ≤ M'.rank := hM'rank
    _ = (compiledTMMatrix numStates numSymbols numTimesteps α).rank := hrank

end PallLean.Paper93.DeepMath.CookLevin

import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetNonzero
import PallLean.Paper93.DeepMath.GadgetRank.RankPosOfNe

namespace PallLean.Paper93.DeepMath.BridgeB

open PallLean.Paper93.DeepMath.GadgetRank

/-- The κ = 2 pocket family's rank equals twice the single-block rank. -/
theorem pocketFamily_two_rank (α : ℝ) (n : ℕ) :
    (pocketFamily α 2 n).rank = 2 * (compiledGadget α n).rank := by
  rw [pocketFamily_rank]

/-- κ = 2 pocket family has rank ≥ 2 for α > 0 and n ≥ 2. -/
theorem pocketFamily_two_rank_ge_two (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    2 ≤ (pocketFamily α 2 n).rank := by
  rw [pocketFamily_two_rank]
  have h1 : 1 ≤ (compiledGadget α n).rank :=
    PallLean.Paper93.DeepMath.GadgetRank.rank_pos_of_ne_zero
      (compiledGadget α n) (compiledGadget_ne_zero α n hα hn)
  linarith

end PallLean.Paper93.DeepMath.BridgeB

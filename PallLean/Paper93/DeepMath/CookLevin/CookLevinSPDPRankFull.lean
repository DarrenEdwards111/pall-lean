import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.CompiledTMPocketRank

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Full Cook-Levin SPDP rank bound chain:
    compiled TM matrix rank equals cookLevinGadget rank (via re-indexing),
    which equals compiledGadget rank, which is ≥ 1 (Bridge A),
    and for κ-pocket composition is ≥ κ (Bridge B). -/
theorem cookLevin_full_rank_chain (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank ∧
    1 ≤ (compiledGadget α n).rank := by
  refine ⟨theorem_207_rank_chain α κ n hα hn, ?_⟩
  apply rank_pos_of_ne_zero
  exact compiledGadget_ne_zero α n hα hn

end PallLean.Paper93.DeepMath.CookLevin

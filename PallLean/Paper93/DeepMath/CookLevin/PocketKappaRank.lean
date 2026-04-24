import PallLean.Paper93.DeepMath.CookLevin.CompiledTMPocketRank
import PallLean.Paper93.DeepMath.CookLevin.CookLevinRank
import PallLean.Paper93.DeepMath.BridgeB.PocketFamily
import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- The paper-§28.3 κ-pocket bound: for a κ-copy pocket family where each block is
    nonzero (α > 0, n ≥ 2), the total rank is at least κ. -/
theorem pocketFamily_total_rank_ge_κ (α : ℝ) (κ n : ℕ)
    (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank := by
  rw [pocketFamily_rank]
  have h_block : 1 ≤ (compiledGadget α n).rank :=
    cookLevinGadget_rank_pos α n hα hn
  calc κ = κ * 1 := (Nat.mul_one κ).symm
    _ ≤ κ * (compiledGadget α n).rank := Nat.mul_le_mul_left κ h_block

end PallLean.Paper93.DeepMath.CookLevin

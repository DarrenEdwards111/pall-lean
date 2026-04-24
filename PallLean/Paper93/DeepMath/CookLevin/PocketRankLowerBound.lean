import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank
import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget
import PallLean.Paper93.DeepMath.CookLevin.CookLevinRank

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- The κ-pocket Cook-Levin family has rank ≥ κ when α > 0 and n ≥ 2. -/
theorem pocketFamily_rank_ge_κ (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank := by
  rw [pocketFamily_rank]
  have h1 : 1 ≤ (compiledGadget α n).rank := by
    -- This is cookLevinGadget_rank_pos, since cookLevinGadget = compiledGadget.
    show 1 ≤ (cookLevinGadget α n).rank
    exact cookLevinGadget_rank_pos α n hα hn
  -- κ * 1 ≤ κ * rank
  calc κ = κ * 1 := (Nat.mul_one κ).symm
    _ ≤ κ * (compiledGadget α n).rank := Nat.mul_le_mul_left κ h1

end PallLean.Paper93.DeepMath.CookLevin

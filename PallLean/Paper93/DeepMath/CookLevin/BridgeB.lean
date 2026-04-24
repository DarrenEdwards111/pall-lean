import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank
import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget
import PallLean.Paper93.DeepMath.GadgetRank.RankPosOfNe

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Paper §28.3 Bridge B: the κ-pocket block-diagonal compiled gadget family has
    rank ≥ κ. -/
theorem bridge_B_kappa_pocket (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank := by
  rw [pocketFamily_rank]
  have h_block : 1 ≤ (compiledGadget α n).rank := by
    apply PallLean.Paper93.DeepMath.GadgetRank.rank_pos_of_ne_zero
    exact compiledGadget_ne_zero α n hα hn
  calc κ = κ * 1 := (Nat.mul_one κ).symm
    _ ≤ κ * (compiledGadget α n).rank := Nat.mul_le_mul_left κ h_block

end PallLean.Paper93.DeepMath.CookLevin

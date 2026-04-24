import PallLean.Paper93.DeepMath.CookLevin.BridgeA
import PallLean.Paper93.DeepMath.CookLevin.BridgeB

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Combined Bridge A + Bridge B: each pocket has rank ≥ 1 (Bridge A), and the κ-pocket
    block-diagonal sum has total rank ≥ κ (Bridge B). -/
theorem bridges_AB_combined (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    1 ≤ (compiledGadget α n).rank ∧ κ ≤ (pocketFamily α κ n).rank := by
  refine ⟨bridge_A_pocket α n hα hn, bridge_B_kappa_pocket α κ n hα hn⟩

end PallLean.Paper93.DeepMath.CookLevin

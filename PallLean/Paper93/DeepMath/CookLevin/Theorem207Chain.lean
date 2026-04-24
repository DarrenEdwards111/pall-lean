import PallLean.Paper93.DeepMath.CookLevin.BridgeA
import PallLean.Paper93.DeepMath.CookLevin.BridgeB

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Paper §28.3/§40 Theorem 207 chain (Lean-side rank bound package):
    combining Bridge A (α > 0 ⇒ each block rank ≥ 1) and Bridge B (κ blocks ⇒ total rank ≥ κ)
    gives `rank(pocketFamily α κ n) ≥ κ`. -/
theorem theorem_207_rank_chain (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank :=
  bridge_B_kappa_pocket α κ n hα hn

end PallLean.Paper93.DeepMath.CookLevin

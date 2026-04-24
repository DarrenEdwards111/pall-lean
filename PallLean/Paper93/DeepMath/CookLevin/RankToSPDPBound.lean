import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- SPDP-style rank bound for κ-pocket compiled family:
    `rank ≥ κ` is the paper's SPDP rank lower bound statement at the compiled gadget level. -/
theorem SPDP_rank_lower_bound (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank := theorem_207_rank_chain α κ n hα hn

/-- Monotonic rank growth: for two pocket counts κ₁ ≤ κ₂, the rank is also ≤. -/
theorem SPDP_rank_monotone (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n)
    (κ₁ κ₂ : ℕ) (hκ : κ₁ ≤ κ₂) :
    κ₁ ≤ (pocketFamily α κ₂ n).rank :=
  le_trans hκ (theorem_207_rank_chain α κ₂ n hα hn)

end PallLean.Paper93.DeepMath.CookLevin

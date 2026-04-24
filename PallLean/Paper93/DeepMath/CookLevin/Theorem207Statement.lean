import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Paper §28.3 / §40 Theorem 207: the κ-pocket Cook-Levin compiled matrix has SPDP-style rank
    bounded below by κ (for each α > 0, n ≥ 2). This is the Lean-side statement of the paper's
    headline rank-lower-bound theorem — the variational analysis of S_NF combined with Bridges A and B. -/
theorem paper_theorem_207 (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank :=
  theorem_207_rank_chain α κ n hα hn

end PallLean.Paper93.DeepMath.CookLevin

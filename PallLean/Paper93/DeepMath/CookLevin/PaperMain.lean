import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Statement
import PallLean.Paper93.DeepMath.CookLevin.RankGrowthPaper
import PallLean.Paper93.DeepMath.CookLevin.CookLevinMainResults

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Paper §28.3 / §40 headline rank chain: for every α > 0, every κ, and every tableau size
    n ≥ 2, the κ-pocket compiled Cook-Levin matrix has rank at least κ. This is the core
    rank lower bound from Paper §28.3 (Bridges A and B composed). -/
theorem paper_headline_rank (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank :=
  paper_theorem_207 α κ n hα hn

end PallLean.Paper93.DeepMath.CookLevin

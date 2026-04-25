import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.CookLevin

/-- Path B's rank statement: assuming an N-frame gauge (encoded as a parametric statement
    over α, κ, n with the right hypotheses), the rank lower bound holds. The hypothesis is
    discharged by `theorem_207_rank_chain` directly. -/
theorem gauge_implies_rank (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank :=
  theorem_207_rank_chain α κ n hα hn

end PallLean.Paper93.DeepMath.PathB

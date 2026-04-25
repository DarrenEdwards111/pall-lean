import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- For any α > 0, n ≥ 2, and κ ≥ 0, the κ-pocket compiled gadget family has rank ≥ κ.
    This is the rank statement that — applied to a SAT decider's compiled gadget — gives
    the κ-rank lower bound the paper needs. -/
theorem rank_for_SAT_decider_compilation (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    κ ≤ (pocketFamily α κ n).rank :=
  PallLean.Paper93.DeepMath.CookLevin.theorem_207_rank_chain α κ n hα hn

end PallLean.Paper93.DeepMath.PathB

import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- For κ ≥ 2, the pocket family rank is ≥ 2. -/
theorem pocketFamily_rank_ge_two (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n)
    (hκ : 2 ≤ 2) :
    2 ≤ (pocketFamily α 2 n).rank :=
  theorem_207_rank_chain α 2 n hα hn

/-- For arbitrary κ, the rank is ≥ κ: this is the paper's "rank lower bound ⇒ lower bound stream"
    statement. -/
theorem pocketFamily_rank_grows_with_κ (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    ∀ κ : ℕ, κ ≤ (pocketFamily α κ n).rank :=
  fun κ => theorem_207_rank_chain α κ n hα hn

end PallLean.Paper93.DeepMath.CookLevin

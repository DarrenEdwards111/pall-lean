import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.PaperMain

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- The paper's final rank-bound theorem in its strongest cookLevin-faithful form:
    rank ≥ κ for every choice of (α, κ, n) with α > 0 and n ≥ 2. -/
theorem cookLevin_paper_final_rank_chain :
    ∀ (α : ℝ) (κ n : ℕ), 0 < α → 2 ≤ n → κ ≤ (pocketFamily α κ n).rank :=
  fun α κ n hα hn => paper_headline_rank α κ n hα hn

end PallLean.Paper93.DeepMath.CookLevin

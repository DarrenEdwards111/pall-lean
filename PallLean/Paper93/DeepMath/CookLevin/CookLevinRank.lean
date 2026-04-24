import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget
import PallLean.Paper93.DeepMath.GadgetRank.RankPosOfNe

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- For `α > 0` and `n ≥ 2`, the Cook-Levin gadget has rank ≥ 1.
    (Full composition: α > 0 → compiledGadget_ne_zero → rank_pos_of_ne_zero.) -/
theorem cookLevinGadget_rank_pos (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    1 ≤ (cookLevinGadget α n).rank := by
  apply rank_pos_of_ne_zero
  exact cookLevinGadget_ne_zero α n hα hn

end PallLean.Paper93.DeepMath.CookLevin

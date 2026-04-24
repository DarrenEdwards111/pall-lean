import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget
import PallLean.Paper93.DeepMath.GadgetRank.RankPosOfNe

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS

/-- Paper §28.3 Bridge A: for each pocket with α > 0 and n ≥ 2, the compiled gadget
    has rank ≥ 1 via the energy-to-rank chain. -/
theorem bridge_A_pocket (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    1 ≤ (cookLevinGadget α n).rank := by
  apply rank_pos_of_ne_zero
  exact cookLevinGadget_ne_zero α n hα hn

/-- Bridge A quantitative: uniform energy bound α > 0 ⇒ rank ≥ 1. -/
theorem bridge_A_energy_to_rank (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    0 < (cookLevinGadget α n).rank := by
  have := bridge_A_pocket α n hα hn
  omega

end PallLean.Paper93.DeepMath.CookLevin

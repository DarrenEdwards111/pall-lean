import PallLean.Paper93.DeepMath.CookLevin.CompiledTM
import PallLean.Paper93.DeepMath.CookLevin.CookLevinRank

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- The SPDP rank bound for the Cook-Levin compiled gadget (Paper §28.3 Bridge A conclusion):
    for α > 0 and tableau size ≥ 2, the compiled Cook-Levin gadget has rank ≥ 1. -/
theorem cookLevin_SPDP_rank_pos (α : ℝ) (n : ℕ)
    (hα : 0 < α) (hn : 2 ≤ n) :
    1 ≤ (cookLevinGadget α n).rank :=
  cookLevinGadget_rank_pos α n hα hn

end PallLean.Paper93.DeepMath.CookLevin

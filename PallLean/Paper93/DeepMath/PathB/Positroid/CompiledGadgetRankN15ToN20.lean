import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_rank_n15 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 15).rank = 15 := compiledGadget_rank_full α 15 hα (by norm_num)

theorem compiledGadget_rank_n16 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 16).rank = 16 := compiledGadget_rank_full α 16 hα (by norm_num)

theorem compiledGadget_rank_n17 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 17).rank = 17 := compiledGadget_rank_full α 17 hα (by norm_num)

theorem compiledGadget_rank_n18 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 18).rank = 18 := compiledGadget_rank_full α 18 hα (by norm_num)

theorem compiledGadget_rank_n19 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 19).rank = 19 := compiledGadget_rank_full α 19 hα (by norm_num)

theorem compiledGadget_rank_n20 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 20).rank = 20 := compiledGadget_rank_full α 20 hα (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid

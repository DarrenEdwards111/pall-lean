import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_rank_n11 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 11).rank = 11 :=
  compiledGadget_rank_full α 11 hα (by norm_num)

theorem compiledGadget_rank_n12 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 12).rank = 12 :=
  compiledGadget_rank_full α 12 hα (by norm_num)

theorem compiledGadget_rank_n13 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 13).rank = 13 :=
  compiledGadget_rank_full α 13 hα (by norm_num)

theorem compiledGadget_rank_n14 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 14).rank = 14 :=
  compiledGadget_rank_full α 14 hα (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid

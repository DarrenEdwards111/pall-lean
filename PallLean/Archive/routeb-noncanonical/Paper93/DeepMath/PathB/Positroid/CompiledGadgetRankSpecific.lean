import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_rank_n2 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 2).rank = 2 :=
  compiledGadget_rank_full α 2 hα (by norm_num)

theorem compiledGadget_rank_n3 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 3).rank = 3 :=
  compiledGadget_rank_full α 3 hα (by norm_num)

theorem compiledGadget_rank_n4 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 4).rank = 4 :=
  compiledGadget_rank_full α 4 hα (by norm_num)

theorem compiledGadget_rank_n5 (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 5).rank = 5 :=
  compiledGadget_rank_full α 5 hα (by norm_num)

theorem compiledGadget_rank_at_alpha_one (n : ℕ) (hn : 1 ≤ n) :
    (compiledGadget 1 n).rank = n :=
  compiledGadget_rank_full 1 n one_pos hn

end PallLean.Paper93.DeepMath.PathB.Positroid

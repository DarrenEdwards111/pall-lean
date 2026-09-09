import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank

namespace ConcretePocketExactRank
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.PathB

/-- Exact rank of the existing concrete gadget, not a replacement invariant. -/
theorem compiled_rank_exact (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    (compiledGadget α n).rank = n := by
  have hd := (compiledGadget_posDef α n hα hn).det_pos
  have hu : IsUnit (compiledGadget α n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hd))
  simpa using Matrix.rank_of_isUnit _ hu

/-- Each pocket is full-rank, so total rank is exactly its ambient dimension. -/
theorem pocket_rank_exact (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    (pocketFamily α κ n).rank = κ * n := by
  rw [pocketFamily_rank, compiled_rank_exact α n hα hn]

end ConcretePocketExactRank
#print axioms ConcretePocketExactRank.compiled_rank_exact
#print axioms ConcretePocketExactRank.pocket_rank_exact

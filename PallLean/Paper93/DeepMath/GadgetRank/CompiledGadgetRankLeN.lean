import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- Rank of compiled gadget is bounded by n (the size of the underlying matrix). -/
theorem compiledGadget_rank_le (α : ℝ) (n : ℕ) :
    (compiledGadget α n).rank ≤ n := by
  have := Matrix.rank_le_card_width (compiledGadget α n)
  simpa [Fintype.card_fin] using this

end PallLean.Paper93.DeepMath.GadgetRank

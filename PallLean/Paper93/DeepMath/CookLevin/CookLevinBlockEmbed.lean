import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget
import PallLean.Paper93.DeepMath.BridgeB.PocketFamily
import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- A single-pocket κ=1 pocket family is just a re-indexed single gadget.
    Specifically, the block-diagonal of one copy equals that copy after
    suitable re-indexing by `Fin n × Fin 1 ≃ Fin n`. -/
theorem pocketFamily_one_rank (α : ℝ) (n : ℕ) :
    (pocketFamily α 1 n).rank = (compiledGadget α n).rank := by
  rw [pocketFamily_rank]
  simp

/-- When κ = 1, the pocket-family rank equals the Cook-Levin single gadget rank. -/
theorem cookLevinGadget_rank_eq_pocketFamily_one (α : ℝ) (n : ℕ) :
    (cookLevinGadget α n).rank = (pocketFamily α 1 n).rank := by
  unfold cookLevinGadget
  rw [pocketFamily_one_rank]

end PallLean.Paper93.DeepMath.CookLevin

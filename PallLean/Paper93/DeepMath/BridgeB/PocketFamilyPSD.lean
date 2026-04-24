import PallLean.Paper93.DeepMath.BridgeB.PocketFamily
import PallLean.Paper93.DeepMath.BridgeB.PosSemidefBlockDiagonal

namespace PallLean.Paper93.DeepMath.BridgeB

open PallLean.Paper93.DeepMath.GadgetRank

/-- The pocket family is PosSemidef whenever each block is. -/
theorem pocketFamily_posSemidef (α : ℝ) (κ n : ℕ)
    (h_block : (compiledGadget α n).PosSemidef) :
    (pocketFamily α κ n).PosSemidef := by
  unfold pocketFamily
  exact posSemidef_blockDiagonal _ (fun _ => h_block)

end PallLean.Paper93.DeepMath.BridgeB

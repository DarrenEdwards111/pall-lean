import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PSDAdd
import PallLean.Paper93.DeepMath.IdentityPSD

namespace PallLean.Paper93.DeepMath.GadgetRank

open PallLean.Paper93.DeepMath PallLean.Paper93.DeepMath.GraphSpectral
  PallLean.Paper93.DeepMath.LPS

/-- The compiled gadget `compiledGadget α n := α • I + L_{K_n}` is PosSemidef
    when `α ≥ 0`, assuming `L_{K_n}` is PosSemidef. -/
theorem compiledGadget_posSemidef (α : ℝ) (n : ℕ) (hα : 0 ≤ α)
    (hL : (laplacian (completeAdj n)).PosSemidef) :
    (compiledGadget α n).PosSemidef := by
  unfold compiledGadget
  apply psd_add
  · -- α • I is PSD when α ≥ 0
    exact identity_posSemidef.smul hα
  · exact hL

end PallLean.Paper93.DeepMath.GadgetRank

import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.GadgetRank.QuadAdd
import PallLean.Paper93.DeepMath.GadgetRank.SmulIdentQuad

namespace PallLean.Paper93.DeepMath.GadgetRank

open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

/-- Quadratic form decomposition for the canonical Cook–Levin α-gadget matrix
    `Q(α,n) := α • I + L_{K_n}`:
    `vᵀ Q(α,n) v = α · ‖v‖² + vᵀ L_{K_n} v`. -/
theorem compiledGadget_quadForm (α : ℝ) (n : ℕ) (v : Fin n → ℝ) :
    ∑ i, v i * ((compiledGadget α n).mulVec v i) =
      α * (∑ i, v i * v i) +
      (∑ i, v i * ((laplacian (completeAdj n)).mulVec v i)) := by
  unfold compiledGadget
  rw [quadForm_add, smul_one_quadForm]

end PallLean.Paper93.DeepMath.GadgetRank

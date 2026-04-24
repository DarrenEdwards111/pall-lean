import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetQuad
import PallLean.Paper93.DeepMath.LPS.KnLaplacianSumZeroQuad

namespace PallLean.Paper93.DeepMath.GadgetRank

open PallLean.Paper93.DeepMath.LPS

theorem compiledGadget_quadForm_sumZero (α : ℝ) (n : ℕ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) :
    ∑ i, v i * ((compiledGadget α n).mulVec v i) = (α + n) * ∑ i, v i * v i := by
  rw [compiledGadget_quadForm, completeAdj_laplacian_sumZero_quadForm n v hv]
  ring

end PallLean.Paper93.DeepMath.GadgetRank

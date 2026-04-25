import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

/-- For α = 0, compiledGadget collapses to the Laplacian. -/
theorem compiledGadget_zero_alpha (n : ℕ) :
    compiledGadget 0 n = laplacian (completeAdj n) := by
  unfold compiledGadget
  simp

/-- For α = 0 and n ≥ 2, compiledGadget is NOT identity (it's the Laplacian, off-diag = -1). -/
theorem compiledGadget_zero_alpha_ne_identity (n : ℕ) (hn : 2 ≤ n) :
    compiledGadget 0 n ≠ (1 : Matrix (Fin n) (Fin n) ℝ) :=
  compiledGadget_ne_identity 0 n hn

end PallLean.Paper93.DeepMath.PathB.Positroid

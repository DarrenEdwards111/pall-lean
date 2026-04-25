import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetOrthogonalEigenvec
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- At n=2, the all-ones eigenvector has eigenvalue α. -/
theorem compiledGadget_n2_allOnes_eigenvalue (α : ℝ) :
    (compiledGadget α 2).mulVec (fun _ : Fin 2 => 1) = (fun _ : Fin 2 => α) :=
  compiledGadget_mulVec_one α 2

/-- At n=2, sum-zero v gives eigenvalue α+2. -/
theorem compiledGadget_n2_sumZero_eigenvalue (α : ℝ) (v : Fin 2 → ℝ) (hv : ∑ i, v i = 0) :
    (compiledGadget α 2).mulVec v = (α + 2) • v :=
  compiledGadget_mulVec_sumZero α 2 v hv

/-- At n=3, the all-ones eigenvector has eigenvalue α. -/
theorem compiledGadget_n3_allOnes_eigenvalue (α : ℝ) :
    (compiledGadget α 3).mulVec (fun _ : Fin 3 => 1) = (fun _ : Fin 3 => α) :=
  compiledGadget_mulVec_one α 3

/-- At n=3, sum-zero v gives eigenvalue α+3. -/
theorem compiledGadget_n3_sumZero_eigenvalue (α : ℝ) (v : Fin 3 → ℝ) (hv : ∑ i, v i = 0) :
    (compiledGadget α 3).mulVec v = (α + 3) • v :=
  compiledGadget_mulVec_sumZero α 3 v hv

end PallLean.Paper93.DeepMath.PathB.Positroid

import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetOrthogonalEigenvec
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_n4_allOnes_eigenvalue (α : ℝ) :
    (compiledGadget α 4).mulVec (fun _ : Fin 4 => 1) = (fun _ : Fin 4 => α) :=
  compiledGadget_mulVec_one α 4

theorem compiledGadget_n5_allOnes_eigenvalue (α : ℝ) :
    (compiledGadget α 5).mulVec (fun _ : Fin 5 => 1) = (fun _ : Fin 5 => α) :=
  compiledGadget_mulVec_one α 5

theorem compiledGadget_n4_sumZero_eigenvalue (α : ℝ) (v : Fin 4 → ℝ) (hv : ∑ i, v i = 0) :
    (compiledGadget α 4).mulVec v = (α + 4) • v :=
  compiledGadget_mulVec_sumZero α 4 v hv

theorem compiledGadget_n5_sumZero_eigenvalue (α : ℝ) (v : Fin 5 → ℝ) (hv : ∑ i, v i = 0) :
    (compiledGadget α 5).mulVec v = (α + 5) • v :=
  compiledGadget_mulVec_sumZero α 5 v hv

end PallLean.Paper93.DeepMath.PathB.Positroid

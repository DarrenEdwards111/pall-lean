import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

theorem compiledGadget_transpose_eq (α : ℝ) (n : ℕ) :
    (compiledGadget α n).transpose = compiledGadget α n :=
  compiledGadget_isSymm α n

theorem compiledGadget_isSymm_again (α : ℝ) (n : ℕ) :
    (compiledGadget α n).IsSymm :=
  compiledGadget_isSymm α n

theorem compiledGadget_entry_symm (α : ℝ) (n : ℕ) (i j : Fin n) :
    compiledGadget α n i j = compiledGadget α n j i := by
  have h := compiledGadget_isSymm α n
  exact (Matrix.IsSymm.apply h i j).symm

end PallLean.Paper93.DeepMath.PathB.Positroid

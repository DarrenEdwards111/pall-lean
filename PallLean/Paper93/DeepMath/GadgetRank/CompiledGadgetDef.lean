import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GadgetRank

open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral

/-- Canonical Cook–Levin compiled gadget matrix parametrised by coupling `α ≥ 0`:
    `Q(α, n) := α • I + L_{K_n}`, where `L_{K_n}` is the Laplacian of the complete
    graph on `Fin n`. This is the §28.3 α-term matrix. -/
def compiledGadget (α : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n)

/-- Symmetry of the compiled gadget. -/
theorem compiledGadget_isSymm (α : ℝ) (n : ℕ) : (compiledGadget α n).IsSymm := by
  unfold compiledGadget
  have h_one_symm : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm := by
    unfold Matrix.IsSymm
    exact Matrix.transpose_one
  have h_lap_symm : (laplacian (completeAdj n)).IsSymm :=
    laplacian_isSymm _ (completeAdj_symm n)
  unfold Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_smul, h_one_symm, h_lap_symm]

end PallLean.Paper93.DeepMath.GadgetRank

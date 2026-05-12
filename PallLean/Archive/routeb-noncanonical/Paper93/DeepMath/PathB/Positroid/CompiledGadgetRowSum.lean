import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.KnLaplacianKernel
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import Mathlib.Data.Matrix.Mul

/-!
# Row sum of `compiledGadget α n` is `α`

The compiled gadget `compiledGadget α n = α • I + L_{K_n}` has constant
row sum `α`: the Laplacian's row sum is zero (its rows sum to zero by
construction), and `α • I`'s row sum at row `i` is `α` (only the
diagonal entry contributes).

The identity `(M.mulVec (fun _ => 1)) i = ∑ j, M i j` lets us express
the row sum as a `mulVec` against the all-ones vector. We then invoke
the eigenvector relation
`compiledGadget_mulVec_one : (compiledGadget α n).mulVec (fun _ => 1)
                              = (fun _ => α)`
to conclude.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Row sum of `compiledGadget α n` at row `i` equals `α` (Laplacian's
    row sum is `0`, and `α • I`'s row sum is `α • 1 = α`). -/
theorem compiledGadget_rowSum_eq_alpha (α : ℝ) (n : ℕ) (i : Fin n) :
    ∑ j, compiledGadget α n i j = α := by
  -- Express the row sum as a `mulVec` against the all-ones vector.
  have h_eq :
      (compiledGadget α n).mulVec (fun _ => (1 : ℝ)) i
        = ∑ j, compiledGadget α n i j := by
    unfold Matrix.mulVec dotProduct
    simp
  rw [← h_eq]
  -- `compiledGadget.mulVec (fun _ => 1) = (fun _ => α)` (eigenvalue `α`).
  rw [show (compiledGadget α n).mulVec (fun _ : Fin n => (1 : ℝ))
        = fun _ : Fin n => α from compiledGadget_mulVec_one α n]

end PallLean.Paper93.DeepMath.PathB.Positroid

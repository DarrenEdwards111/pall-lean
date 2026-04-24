import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.BridgeB

open PallLean.Paper93.DeepMath.GadgetRank

/-- Uniform κ-pocket Cook-Levin compiled gadget: block-diagonal sum of κ copies
    of `compiledGadget α n`. Models the paper §28.3 block structure where each
    pocket contributes independently to the total quadratic form. -/
def pocketFamily (α : ℝ) (κ n : ℕ) :
    Matrix (Fin n × Fin κ) (Fin n × Fin κ) ℝ :=
  Matrix.blockDiagonal (fun _ : Fin κ => compiledGadget α n)

/-- The pocket family is symmetric. -/
theorem pocketFamily_isSymm (α : ℝ) (κ n : ℕ) : (pocketFamily α κ n).IsSymm := by
  -- Unfold the definition of `pocketFamily` and of `IsSymm`, reducing to the
  -- transpose equation.
  unfold pocketFamily
  unfold Matrix.IsSymm
  -- `Matrix.blockDiagonal_transpose` rewrites the transpose of a block-diagonal
  -- matrix as the block-diagonal of the pointwise transposes.
  rw [Matrix.blockDiagonal_transpose]
  -- Each block is symmetric, so its transpose equals itself.
  have hblock : ∀ k : Fin κ,
      Matrix.transpose (compiledGadget α n) = compiledGadget α n :=
    fun _ => compiledGadget_isSymm α n
  -- Turn the pointwise equation into a function-level equation, then apply it.
  have hfun :
      (fun k : Fin κ => Matrix.transpose (compiledGadget α n))
        = (fun _ : Fin κ => compiledGadget α n) :=
    funext hblock
  rw [hfun]

end PallLean.Paper93.DeepMath.BridgeB

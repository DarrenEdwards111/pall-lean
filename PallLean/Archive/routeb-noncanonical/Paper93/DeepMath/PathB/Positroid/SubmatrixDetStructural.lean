import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Structural diagonal entry of principal submatrices of the compiled gadget

We record a kernel-only structural fact about principal submatrices of
`compiledGadget α n`: the diagonal entry of the principal submatrix at
any nonempty index family `J : Finset (Fin n)` is `α + (n - 1)`, the
same diagonal value carried by the ambient `compiledGadget α n`.

The principal submatrix at `J` indexed by `(k : J)` and `(k : J)` along
both rows and columns is, by `Matrix.submatrix_apply`, equal to the
ambient `(compiledGadget α n) k.val k.val`. By the previously proved
`compiledGadget_diagonal`, this equals `α + (n - 1)`. The submatrix is
indexed over `J` (the smaller index set), but each diagonal entry is
inherited verbatim from the ambient gadget at the embedded index
`k.val : Fin n`.

This is a structural ingredient for analysing `compiledGadget`-type
principal minors at arbitrary subsets `J ⊆ Fin n`: the off-diagonal
entries are `-1` and the diagonal entries are `α + (n - 1)`, exactly
as in the ambient `compiledGadget`, but on the smaller index set.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Structural diagonal entry of a principal submatrix.**

For every Reynolds-free coupling `α : ℝ`, every dimension `n : ℕ`,
every subset `J : Finset (Fin n)`, and every `i : J`, the `(i, i)`
entry of the principal submatrix of `compiledGadget α n` indexed by
`J` along both axes equals `α + (n - 1)`.

The principal submatrix is `(compiledGadget α n).submatrix r r`, where
`r : J → Fin n` is the canonical inclusion `k ↦ k.val`. By the
defining `Matrix.submatrix_apply`, the `(i, i)` entry unfolds to
`compiledGadget α n i.val i.val`, which equals `α + (n - 1)` by
`compiledGadget_diagonal`. -/
theorem compiledGadget_principal_submatrix_diag
    (α : ℝ) (n : ℕ) (J : Finset (Fin n)) (i : J) :
    ((compiledGadget α n).submatrix
      (fun k : J => (k.val : Fin n)) (fun k : J => (k.val : Fin n))) i i
        = α + ((n : ℝ) - 1) := by
  show compiledGadget α n i.val i.val = α + ((n : ℝ) - 1)
  exact compiledGadget_diagonal α n i.val

end PallLean.Paper93.DeepMath.PathB.Positroid

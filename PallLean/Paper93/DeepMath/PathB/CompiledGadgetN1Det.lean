import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Closed-form determinant of the 1×1 compiled gadget

We prove the explicit formula

`(compiledGadget α 1).det = α`

for the 1×1 instantiation of the Cook–Levin compiled gadget
`compiledGadget α 1 = α • I + L_{K_1}`. Since `K_1` has no edges,
`L_{K_1} = 0`, so the gadget reduces to the 1×1 matrix `[[α]]`, whose
determinant is `α`.

The proof proceeds by:

1. Using `Matrix.det_fin_one` to reduce `det A` to `A 0 0`.
2. Substituting the diagonal entry via `compiledGadget_diagonal`,
   which gives `α + ((1 : ℝ) - 1) = α + 0 = α`.
3. Algebraic simplification via `norm_num`.

We also derive:

* the characterisation
  `(compiledGadget α 1).det = 1 ↔ α = 1`, showing that `α = 1` is the
  unique coupling producing determinant `1` in the 1×1 case; and
* the existence statement `(compiledGadget 1 1).det = 1`, the
  immediate `α = 1` instantiation.

Namespace: `PallLean.Paper93.DeepMath.PathB`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Closed-form determinant of the 1×1 compiled gadget.**

For every coupling `α : ℝ`, the determinant of the 1×1 compiled gadget
`compiledGadget α 1 = α • I + L_{K_1}` equals `α`.

The proof uses `Matrix.det_fin_one` to reduce the determinant to the
single `(0, 0)` entry, then substitutes the diagonal value
`α + ((1 : ℝ) - 1) = α` via `compiledGadget_diagonal`. -/
theorem compiledGadget_1x1_det (α : ℝ) :
    (compiledGadget α 1).det = α := by
  rw [Matrix.det_fin_one]
  -- `(compiledGadget α 1) 0 0 = α + ((1 : ℝ) - 1) = α + 0 = α`
  -- since `K_1` has no edges, so its Laplacian diagonal entry is `0`.
  rw [compiledGadget_diagonal]
  norm_num

/-- **Determinant-equals-one characterisation for the 1×1 gadget.**

For the 1×1 compiled gadget, the determinant equals `1` if and only if
the coupling `α` equals `1`.

This is the 1×1 analogue of the `Sqrt2MinusOne` characterisation for
the 2×2 case: the determinant is a linear (here, identity) function of
`α`, and the equation `α = 1` is trivially solvable. -/
theorem compiledGadget_1x1_det_eq_one_iff (α : ℝ) :
    (compiledGadget α 1).det = 1 ↔ α = 1 := by
  rw [compiledGadget_1x1_det]

/-- **Existence: the 1×1 gadget at `α = 1` has determinant `1`.**

Direct corollary of `compiledGadget_1x1_det_eq_one_iff`, applied at
`α = 1`. This is the 1×1 instantiation of the "unique-determinant
existence" witness used in the Route-B chain. -/
theorem compiledGadget_1x1_det_one_at_alpha_one :
    (compiledGadget 1 1).det = 1 :=
  (compiledGadget_1x1_det_eq_one_iff 1).mpr rfl

end PallLean.Paper93.DeepMath.PathB

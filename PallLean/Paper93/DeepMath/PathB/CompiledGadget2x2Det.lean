import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Explicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Closed-form determinant of the 2×2 compiled gadget

We prove the explicit formula

`(compiledGadget α 2).det = α * (α + 2)`

for the 2×2 instantiation of the Cook–Levin compiled gadget
`compiledGadget α 2 = α • I + L_{K_2}`, which evaluates to the matrix

```
    ⎡ α + 1   −1   ⎤
    ⎣  −1   α + 1  ⎦
```

The proof proceeds by:

1. Using `Matrix.det_fin_two` to reduce `det A` to
   `A 0 0 * A 1 1 - A 0 1 * A 1 0`.
2. Substituting the explicit entries from
   `CompiledGadget2x2Explicit.lean`:
   * Diagonal entries: `compiledGadget_2x2_diag` gives `α + 1`.
   * Off-diagonal entries: `compiledGadget_2x2_off_diag_01` and
     `compiledGadget_2x2_off_diag_10` give `-1`.
3. Algebraic simplification: `(α + 1)² − 1 = α² + 2α = α(α + 2)`.

We also derive the corollary that the determinant is strictly positive
for `α > 0`, since both `α` and `α + 2` are positive.

Namespace: `PallLean.Paper93.DeepMath.PathB`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Closed-form determinant of the 2×2 compiled gadget.**

For every coupling `α : ℝ`, the determinant of the 2×2 compiled gadget
`compiledGadget α 2 = α • I + L_{K_2}` equals `α * (α + 2)`.

Equivalently, `det = (α + 1)² − 1 = α² + 2α`.

The proof uses `Matrix.det_fin_two` to expand the determinant into
`A 0 0 * A 1 1 − A 0 1 * A 1 0`, substitutes the diagonal entries
`α + 1` (via `compiledGadget_2x2_diag`) and the off-diagonal entries
`-1` (via `compiledGadget_2x2_off_diag_01` and
`compiledGadget_2x2_off_diag_10`), and simplifies using `ring`. -/
theorem compiledGadget_2x2_det (α : ℝ) :
    (compiledGadget α 2).det = α * (α + 2) := by
  rw [Matrix.det_fin_two]
  -- Diagonal entries are `α + 1` from `compiledGadget_2x2_diag`.
  have h00 : compiledGadget α 2 (0 : Fin 2) (0 : Fin 2) = α + 1 :=
    compiledGadget_2x2_diag α 0
  have h11 : compiledGadget α 2 (1 : Fin 2) (1 : Fin 2) = α + 1 :=
    compiledGadget_2x2_diag α 1
  -- Off-diagonal entries are `-1` from `compiledGadget_2x2_off_diag_*`.
  have h01 : compiledGadget α 2 (0 : Fin 2) (1 : Fin 2) = -1 :=
    compiledGadget_2x2_off_diag_01 α
  have h10 : compiledGadget α 2 (1 : Fin 2) (0 : Fin 2) = -1 :=
    compiledGadget_2x2_off_diag_10 α
  rw [h00, h11, h01, h10]
  ring

/-- **Positivity of the 2×2 compiled gadget determinant for `α > 0`.**

For every coupling `α > 0`, the determinant of `compiledGadget α 2`
is strictly positive.

This follows from the closed-form `det = α * (α + 2)`: both factors are
positive when `α > 0` (since `α + 2 > 2 > 0`), so the product is
positive.

Note: For `α = 0`, the 2×2 compiled gadget is exactly the Laplacian
`L_{K_2}`, which has a one-dimensional kernel (constant vectors), so
`det = 0`. The condition `det = 1` would force `α² + 2α − 1 = 0`, i.e.
`α = √2 − 1` (the positive root). -/
theorem compiledGadget_2x2_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 2).det := by
  rw [compiledGadget_2x2_det]
  -- `0 < α * (α + 2)` since `α > 0` and `α + 2 > 0`.
  have h1 : 0 < α + 2 := by linarith
  exact mul_pos hα h1

end PallLean.Paper93.DeepMath.PathB

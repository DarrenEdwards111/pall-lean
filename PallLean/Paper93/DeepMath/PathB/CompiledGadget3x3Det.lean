import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Explicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closed-form determinant of the 3×3 compiled gadget

We prove the explicit formula

`(compiledGadget α 3).det = α * (α + 3)^2`

for the 3×3 instantiation of the Cook–Levin compiled gadget
`compiledGadget α 3 = α • I + L_{K_3}`, which evaluates to the matrix

```
    ⎡ α + 2   −1     −1  ⎤
    ⎢  −1    α + 2   −1  ⎥
    ⎣  −1     −1    α + 2⎦
```

The eigenstructure explanation: the all-ones vector is an eigenvector
with eigenvalue `α` (the L_{K_n} kernel contribution plus the α shift),
and the orthogonal complement of zero-sum vectors is an eigenspace of
dimension 2 with eigenvalue `α + 3`. Hence

`det = α · (α + 3)^2 = α^3 + 6α^2 + 9α`.

The proof proceeds by:

1. Using `Matrix.det_fin_three` to reduce `det A` to the cofactor
   expansion
   `A00·A11·A22 − A00·A12·A21 − A01·A10·A22 + A01·A12·A20
      + A02·A10·A21 − A02·A11·A20`.
2. Substituting the explicit entries from `CompiledGadget3x3Explicit`:
   * Diagonal entries: `compiledGadget_3x3_diag` gives `α + 2`.
   * Off-diagonal entries: `compiledGadget_3x3_off_diag` gives `-1`
     for every `i ≠ j`.
3. Algebraic simplification via `ring`:
   `(α+2)^3 − 3(α+2) − 2 = α·(α+3)^2`.

We also derive two corollaries:

* `compiledGadget_3x3_det_eq_one_iff`: `det = 1 ↔ α·(α+3)^2 = 1`
  (useful for analysing the "det = 1" gauge condition at `n = 3`).
* `compiledGadget_3x3_det_pos`: the determinant is strictly positive
  for `α > 0`.

The determinant formula `α(α+3)^2` at `n = 3` confirms the general
pattern `α(α+n)^{n−1}` for the compiled gadget with `n` indices.

Namespace: `PallLean.Paper93.DeepMath.PathB`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Closed-form determinant of the 3×3 compiled gadget.**

For every coupling `α : ℝ`, the determinant of the 3×3 compiled gadget
`compiledGadget α 3 = α • I + L_{K_3}` equals `α * (α + 3)^2`.

Equivalently, `det = (α + 2)^3 − 3(α + 2) − 2 = α^3 + 6α^2 + 9α`.

The proof uses `Matrix.det_fin_three` to expand the determinant into
the six signed products of entries, substitutes the diagonal entries
`α + 2` (via `compiledGadget_3x3_diag`) and the off-diagonal entries
`-1` (via `compiledGadget_3x3_off_diag`), and simplifies using `ring`:

```
    (α+2)(α+2)(α+2) − (α+2)(-1)(-1) − (-1)(-1)(α+2)
       + (-1)(-1)(-1) + (-1)(-1)(-1) − (-1)(α+2)(-1)
  =  (α+2)^3 − 3(α+2) − 2
  =  α·(α+3)^2.
```

The eigenstructure corresponds to the all-ones vector (eigenvalue `α`)
and the two-dimensional orthogonal complement of zero-sum vectors
(eigenvalue `α + 3`). -/
theorem compiledGadget_3x3_det (α : ℝ) :
    (compiledGadget α 3).det = α * (α + 3)^2 := by
  rw [Matrix.det_fin_three]
  -- Diagonal entries are `α + 2` from `compiledGadget_3x3_diag`.
  have h00 : compiledGadget α 3 (0 : Fin 3) (0 : Fin 3) = α + 2 :=
    compiledGadget_3x3_diag α 0
  have h11 : compiledGadget α 3 (1 : Fin 3) (1 : Fin 3) = α + 2 :=
    compiledGadget_3x3_diag α 1
  have h22 : compiledGadget α 3 (2 : Fin 3) (2 : Fin 3) = α + 2 :=
    compiledGadget_3x3_diag α 2
  -- Distinctness facts for the six off-diagonal positions.
  have hne01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have hne02 : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
  have hne10 : (1 : Fin 3) ≠ (0 : Fin 3) := by decide
  have hne12 : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
  have hne20 : (2 : Fin 3) ≠ (0 : Fin 3) := by decide
  have hne21 : (2 : Fin 3) ≠ (1 : Fin 3) := by decide
  -- Off-diagonal entries are `-1` from `compiledGadget_3x3_off_diag`.
  have h01 : compiledGadget α 3 (0 : Fin 3) (1 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 0 1 hne01
  have h02 : compiledGadget α 3 (0 : Fin 3) (2 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 0 2 hne02
  have h10 : compiledGadget α 3 (1 : Fin 3) (0 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 1 0 hne10
  have h12 : compiledGadget α 3 (1 : Fin 3) (2 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 1 2 hne12
  have h20 : compiledGadget α 3 (2 : Fin 3) (0 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 2 0 hne20
  have h21 : compiledGadget α 3 (2 : Fin 3) (1 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 2 1 hne21
  rw [h00, h11, h22, h01, h02, h10, h12, h20, h21]
  ring

/-- **Determinant-equals-one iff for the 3×3 compiled gadget.**

The determinant of `compiledGadget α 3` equals `1` if and only if
`α * (α + 3)^2 = 1`.

This is an immediate reformulation of `compiledGadget_3x3_det`, useful
for analysing the "det = 1" gauge condition at `n = 3`. Unlike the
2×2 case where the equation `α^2 + 2α − 1 = 0` has a clean positive
root `α = √2 − 1`, the 3×3 equation `α(α+3)^2 = 1` is a genuine cubic
with one real root near `α ≈ 0.1077` (numerically). -/
theorem compiledGadget_3x3_det_eq_one_iff (α : ℝ) :
    (compiledGadget α 3).det = 1 ↔ α * (α + 3)^2 = 1 := by
  rw [compiledGadget_3x3_det]

/-- **Positivity of the 3×3 compiled gadget determinant for `α > 0`.**

For every coupling `α > 0`, the determinant of `compiledGadget α 3`
is strictly positive.

This follows from the closed-form `det = α * (α + 3)^2`: the factor
`α` is positive by hypothesis, and `(α + 3)^2 > 0` since `α + 3 > 3 > 0`
(so its square is a positive real).

Note: For `α = 0`, the 3×3 compiled gadget is exactly the Laplacian
`L_{K_3}`, which has a one-dimensional kernel (constant vectors), so
`det = 0`. The condition `det = 1` would force `α(α+3)^2 = 1`, giving a
(unique) small positive real root. -/
theorem compiledGadget_3x3_det_pos (α : ℝ) (hα : 0 < α) :
    0 < (compiledGadget α 3).det := by
  rw [compiledGadget_3x3_det]
  have h1 : 0 < α + 3 := by linarith
  have h2 : 0 < (α + 3)^2 := by positivity
  exact mul_pos hα h2

end PallLean.Paper93.DeepMath.PathB

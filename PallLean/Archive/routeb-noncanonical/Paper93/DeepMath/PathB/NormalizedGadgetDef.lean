import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The diagonal-normalized compiled gadget

For a positive-definite matrix `M` with positive diagonals `M i i > 0`, the
*diagonal normalization* is `D^{-1/2} M D^{-1/2}` where `D = diag(M)`. The
resulting matrix has unit diagonal entries.

For `compiledGadget α n`, the diagonal is the constant `α + (n-1)` at every
index `i`. Letting `c := α + (n-1) > 0`, the normalization simplifies to a
scalar multiplication: `(1/c) • compiledGadget α n`. This pragmatic definition
avoids introducing square roots while still producing a unit-diagonal matrix.

We prove:
* `normalizedGadget_diagonal` — the diagonal entry is `1` whenever
  `α + (n-1) > 0`.
* `normalizedGadget_diag_pos_when_alpha_pos` — sufficient positivity in terms
  of `α > 0` and `n ≥ 1`.
* `normalizedGadget_diagonal_eq_one` — combination of the above two.
* `normalizedGadget_isSymm` — symmetry of the normalized gadget.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- The diagonal-normalized compiled gadget: `(1/(α+(n-1))) • compiledGadget α n`.
    Has all-ones diagonal when `α + (n-1) > 0`. -/
noncomputable def normalizedGadget (α : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / (α + ((n : ℝ) - 1))) • compiledGadget α n

/-- **Diagonal of the normalized gadget.**

When `α + (n-1) > 0`, every diagonal entry of `normalizedGadget α n` equals `1`.
This is the defining feature of diagonal normalization. -/
theorem normalizedGadget_diagonal (α : ℝ) (n : ℕ) (i : Fin n)
    (hpos : 0 < α + ((n : ℝ) - 1)) :
    normalizedGadget α n i i = 1 := by
  unfold normalizedGadget
  -- ((1/c) • M) i i = (1/c) * M i i = (1/c) * c = 1
  rw [Matrix.smul_apply, compiledGadget_diagonal]
  have hne : α + ((n : ℝ) - 1) ≠ 0 := ne_of_gt hpos
  show (1 / (α + ((n : ℝ) - 1))) * (α + ((n : ℝ) - 1)) = 1
  field_simp

/-- **Sufficient positivity of `α + (n-1)`.**

Whenever `α > 0` and `n ≥ 1`, the diagonal value `α + (n - 1)` is positive. -/
theorem normalizedGadget_diag_pos_when_alpha_pos
    (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    0 < α + ((n : ℝ) - 1) := by
  have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- **Diagonal equals one** under the standard hypotheses `α > 0` and `n ≥ 1`. -/
theorem normalizedGadget_diagonal_eq_one
    (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) (i : Fin n) :
    normalizedGadget α n i i = 1 :=
  normalizedGadget_diagonal α n i
    (normalizedGadget_diag_pos_when_alpha_pos α n hα hn)

/-- **Symmetry of the normalized gadget.**

Since the normalized gadget is a scalar multiple of `compiledGadget α n`,
which is symmetric, the result is also symmetric. -/
theorem normalizedGadget_isSymm (α : ℝ) (n : ℕ) :
    (normalizedGadget α n).IsSymm := by
  unfold normalizedGadget
  exact (compiledGadget_isSymm α n).smul _

end PallLean.Paper93.DeepMath.PathB

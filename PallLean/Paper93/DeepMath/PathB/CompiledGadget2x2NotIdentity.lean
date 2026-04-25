import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Explicit
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The 2×2 compiled gadget is never the identity matrix

This file shows that the 2×2 compiled gadget
`compiledGadget α 2 = α • I + L_{K_2}`
is **never** equal to the identity matrix `(1 : Matrix (Fin 2) (Fin 2) ℝ)`,
regardless of the choice of `α : ℝ`.

The reason is purely structural: the off-diagonal `(0,1)` entry of the
compiled gadget is `-1` (independent of `α`, by
`compiledGadget_2x2_off_diag_01`), whereas the off-diagonal entry of the
identity matrix is `0`. Hence the two matrices disagree at `(0,1)` for
every `α`.

As a strengthened existential consequence, we package this with the
positive-definiteness of `compiledGadget 1 2` to obtain a non-trivial
positive-definite gauge witness for the satFamily at `n = 2`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **The 2×2 compiled gadget is never the identity.**

For every `α : ℝ`, the 2×2 compiled gadget is distinct from the
identity matrix on `Fin 2`. The proof compares the `(0,1)` entries:

* `compiledGadget α 2 0 1 = -1` by `compiledGadget_2x2_off_diag_01`,
* `(1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0` by `Matrix.one_apply_ne`,

and these two values are unequal in `ℝ`. -/
theorem compiledGadget_2x2_ne_identity (α : ℝ) :
    compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h_eq
  -- Compare entry (0,1): compiledGadget = -1, identity = 0.
  have h01 : compiledGadget α 2 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    rw [h_eq]
  rw [compiledGadget_2x2_off_diag_01] at h01
  -- (1 : Matrix _ _ ℝ) 0 1 = 0 since 0 ≠ 1 in `Fin 2`.
  have h_one : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 :=
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)
  rw [h_one] at h01
  -- h01 : (-1 : ℝ) = 0
  linarith

/-- **Existence of a non-trivial positive-definite gauge witness at `n = 2`.**

There exists a strictly positive `α` such that `compiledGadget α 2`
is *not* the identity matrix and is positive definite. Concretely we
choose `α = 1`: positivity of `1` gives `0 < 1`, the previous theorem
yields the non-identity property, and `compiledGadget_posDef` (with
`hα := one_pos` and `hn : 1 ≤ 2`) supplies the positive definiteness.

This is the strengthened existential statement obtained by combining
`compiledGadget_2x2_ne_identity` with the Path B positive-definiteness
result. -/
theorem n2_nontrivial_gauge_witness_exists :
    ∃ α : ℝ, 0 < α ∧
      compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      (compiledGadget α 2).PosDef := by
  refine ⟨1, one_pos, compiledGadget_2x2_ne_identity 1, ?_⟩
  exact compiledGadget_posDef 1 2 one_pos (by norm_num)

end PallLean.Paper93.DeepMath.PathB

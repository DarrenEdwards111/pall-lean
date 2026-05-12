import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Structural barrier: literal `compiledGadget α n` cannot serve as a gauge
  for non-trivial families when `n ≥ 3`.

The §28.3 compiled gadget has diagonal entries
`compiledGadget α n i i = α + (n - 1)`.

For a principal minor at the singleton `{i}` to equal `1` (the unit
singleton minor condition required for many gauge constructions), one
would need `compiledGadget α n i i = 1`, equivalently `α = 2 - n`.
For `n ≥ 3` this forces `α ≤ -1 < 0`, breaking positive-definiteness.

So when `α > 0` and `n ≥ 3` the literal `compiledGadget α n` cannot
satisfy the unit singleton-minor condition at any index, while the
identity matrix `1` trivially satisfies that condition at every index.
This explains why the gauge-witness construction in the SAT family must
use the identity (or another transformed/normalised matrix) rather than
the literal §28.3 quadratic-form matrix `compiledGadget α n`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Singleton-minor obstruction for the literal compiled gadget.**

For `n ≥ 3` and any `α > 0`, the diagonal entry
`compiledGadget α n i i = α + (n - 1)` is at least `0 + 2 = 2` (in
fact strictly greater than `2` since `α > 0`), so it can never equal
`1`. Hence the literal `compiledGadget α n` cannot satisfy the unit
singleton principal-minor condition at any index `i`, for any positive
coupling `α` once `n ≥ 3`. -/
theorem compiledGadget_singleton_minor_obstruction
    (n : ℕ) (hn : 3 ≤ n) (α : ℝ) (i : Fin n) (hα : 0 < α) :
    compiledGadget α n i i ≠ 1 := by
  -- Use the explicit diagonal formula `compiledGadget α n i i = α + (n - 1)`.
  have hdiag : compiledGadget α n i i = α + ((n : ℝ) - 1) :=
    compiledGadget_diagonal α n i
  -- Cast `3 ≤ n` to the real numbers, giving `(n : ℝ) ≥ 3` hence `(n : ℝ) - 1 ≥ 2`.
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Combine `α > 0` and `(n : ℝ) - 1 ≥ 2` to conclude `α + ((n : ℝ) - 1) > 1`.
  intro hEq
  rw [hdiag] at hEq
  -- Now `hEq : α + ((n : ℝ) - 1) = 1`, but `α > 0` and `(n : ℝ) - 1 ≥ 2`.
  linarith

/-- **Identity succeeds where the literal compiled gadget fails.**

For `n ≥ 3` and any positive coupling `α`, the literal `compiledGadget α n`
fails to make any singleton minor `(i, i)` equal to `1`, while the identity
matrix `(1 : Matrix (Fin n) (Fin n) ℝ)` makes every singleton minor equal
to `1`.

This explains why a non-vacuous gauge witness for a family containing
singleton index sets must use the identity (or a transformed/normalised
matrix), not the literal §28.3 compiled-gadget matrix. The §7.1 positroid
construction operates in a different coordinate system from the §28.3
quadratic form, which is precisely why the gauge-witness chain can succeed
on one side and not on the other. -/
theorem identity_succeeds_where_compiledGadget_fails
    (n : ℕ) (hn : 3 ≤ n) (α : ℝ) (hα : 0 < α) :
    (∀ i : Fin n, compiledGadget α n i i ≠ 1) ∧
      (∀ i : Fin n, (1 : Matrix (Fin n) (Fin n) ℝ) i i = 1) := by
  refine ⟨fun i => compiledGadget_singleton_minor_obstruction n hn α i hα, ?_⟩
  intro i
  simp [Matrix.one_apply_eq]

end PallLean.Paper93.DeepMath.PathB

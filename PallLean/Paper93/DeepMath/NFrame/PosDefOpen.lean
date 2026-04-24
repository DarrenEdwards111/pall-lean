import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Star
import Mathlib.Data.Real.StarOrdered

/-!
# Convexity of the set of positive definite matrices

The file name is `PosDefOpen` for historical reasons. The *openness* of
`{A | A.PosDef}` in the ambient space `Matrix (Fin n) (Fin n) ℝ` is
*not* true in general: the positive-definite condition includes
Hermitian-ness (symmetry over `ℝ`), which cuts out a proper closed linear
subspace whose interior in the full matrix space is empty (for `n ≥ 2`).
Consequently, no `IsOpen {A | A.PosDef}` statement in the ambient matrix
space is available either in Mathlib or in this development.

We therefore package the weaker, genuinely true convexity statement:

* `posDef_set_convex`: the set `{A | A.PosDef}` is convex as a subset of
  `Matrix (Fin n) (Fin n) ℝ`.

The proof combines `Matrix.PosDef.smul` and `Matrix.PosDef.add` from
Mathlib, with careful handling of the degenerate endpoints `a = 0` and
`b = 0` of the convex combination `a • x + b • y`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open Matrix

/-- The set `{A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}` is convex:
for any two positive-definite matrices `A, B` and any scalars
`a, b ≥ 0` with `a + b = 1`, the convex combination `a • A + b • B`
is again positive definite.

This is the genuinely true replacement for the (false, for `n ≥ 2`)
statement that the positive-definite locus is open in the ambient
matrix space.

Proof sketch. If both `a` and `b` are strictly positive we combine
`Matrix.PosDef.smul` (scaling preserves positive definiteness when the
scalar is `> 0`) with `Matrix.PosDef.add` (sum of two positive-definite
matrices is positive definite). The degenerate endpoints `a = 0` or
`b = 0` are handled separately: from `a + b = 1` exactly one of them
equals `1`, and `1 • x = x`, `0 • x = 0`, so the combination equals
the other endpoint, which is already positive definite. -/
theorem posDef_set_convex {n : ℕ} :
    Convex ℝ {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef} := by
  -- Unfold convexity to the pointwise combination formulation.
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  -- `hx : x.PosDef`, `hy : y.PosDef`; `ha : 0 ≤ a`, `hb : 0 ≤ b`, `hab : a + b = 1`.
  -- Split on whether `a = 0` or `a > 0`.
  rcases lt_or_eq_of_le ha with ha_pos | ha_zero
  · -- Case `0 < a`.  Split further on `b`.
    rcases lt_or_eq_of_le hb with hb_pos | hb_zero
    · -- Case `0 < a` and `0 < b`: use smul + add directly.
      have hax : (a • x).PosDef := hx.smul ha_pos
      have hby : (b • y).PosDef := hy.smul hb_pos
      exact hax.add hby
    · -- Case `0 < a` and `b = 0`.  Then `a = 1`, so `a • x + b • y = x`.
      have hb_eq : b = 0 := hb_zero.symm
      have ha_eq : a = 1 := by
        have : a + 0 = 1 := by rw [← hb_eq]; exact hab
        simpa using this
      -- Rewrite the combination.
      have : a • x + b • y = x := by
        rw [ha_eq, hb_eq, one_smul, zero_smul, add_zero]
      -- Conclude membership.
      show (a • x + b • y).PosDef
      rw [this]
      exact hx
  · -- Case `a = 0`.  Then `b = 1`, so `a • x + b • y = y`.
    have ha_eq : a = 0 := ha_zero.symm
    have hb_eq : b = 1 := by
      have : 0 + b = 1 := by rw [← ha_eq]; exact hab
      simpa using this
    have : a • x + b • y = y := by
      rw [ha_eq, hb_eq, zero_smul, one_smul, zero_add]
    show (a • x + b • y).PosDef
    rw [this]
    exact hy

end PallLean.Paper93.DeepMath.NFrame

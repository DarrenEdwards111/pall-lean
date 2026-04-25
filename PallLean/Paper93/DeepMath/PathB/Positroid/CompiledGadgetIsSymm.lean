import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetStructIdentity
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Symmetry of the compiled gadget via the structural entrywise identity

This file provides a self-contained, structural-identity-based proof of
the symmetry of the compiled gadget matrix

  `compiledGadget α n = α • I + L_{K_n}`

needed for the spectral theorem path. The entrywise structural identity
established in `CompiledGadgetStructIdentity` shows

  `compiledGadget α n i j = (α + n) * (if i = j then 1 else 0) - 1`,

which is manifestly symmetric in `(i, j)` since the predicate `i = j`
is symmetric. We package this as both a `Matrix.IsSymm` statement and
the explicit transpose-equals-self identity.

These are independent re-derivations of the symmetry results already
present (under similar names) in `CompiledGadgetDef.lean` and
`CompiledGadgetTranspose.lean`; they give a structural proof route
that proceeds through `compiledGadget_struct_identity` rather than
through the additive decomposition of the smul of the identity and the
Laplacian. This is useful for the spectral theorem path, which prefers
to reason directly about the closed-form entries of the gadget.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **The compiled gadget is symmetric.**

For all `α : ℝ` and `n : ℕ`, the matrix `compiledGadget α n` is
symmetric in the sense of `Matrix.IsSymm`, i.e.
`(compiledGadget α n)ᵀ = compiledGadget α n`.

The proof goes via the structural entrywise identity
`compiledGadget_struct_identity`: each entry equals
`(α + n) * (if i = j then 1 else 0) - 1`, which is symmetric in
`(i, j)` because the equality predicate `i = j` is symmetric. -/
theorem compiledGadget_isSymm (α : ℝ) (n : ℕ) :
    (compiledGadget α n).IsSymm := by
  unfold Matrix.IsSymm
  funext i j
  rw [Matrix.transpose_apply]
  rw [compiledGadget_struct_identity α n j i]
  rw [compiledGadget_struct_identity α n i j]
  -- Both sides reduce to `(α + n) * (if i = j then 1 else 0) - 1`
  -- after using symmetry of equality `j = i ↔ i = j`.
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ j = i := fun h => hij h.symm
    simp [hij, hji]

/-- **The compiled gadget equals its own transpose.**

A direct restatement of `compiledGadget_isSymm` unfolding the
definition `Matrix.IsSymm A := Aᵀ = A`. This is the form most
convenient for the spectral theorem path, which manipulates
`(compiledGadget α n)ᵀ` explicitly. -/
theorem compiledGadget_transpose_eq (α : ℝ) (n : ℕ) :
    (compiledGadget α n)ᵀ = compiledGadget α n :=
  compiledGadget_isSymm α n

end PallLean.Paper93.DeepMath.PathB.Positroid

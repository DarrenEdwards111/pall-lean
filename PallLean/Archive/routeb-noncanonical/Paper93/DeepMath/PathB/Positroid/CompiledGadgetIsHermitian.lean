import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetIsSymm
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetStructIdentity
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Tactic.Ring

/-!
# Hermitian property of the compiled gadget over ℝ

This file establishes that the compiled gadget matrix

  `compiledGadget α n = α • I + L_{K_n}`

over the real numbers is Hermitian in the sense of `Matrix.IsHermitian`,
i.e. `(compiledGadget α n)ᴴ = compiledGadget α n`.

This is required as input for the spectral theorem composition path:
`Matrix.IsHermitian.eigenvalues` and the associated diagonalisation
results in `Mathlib.Analysis.Matrix.Spectrum` consume an
`IsHermitian` hypothesis, so the symmetry of the gadget alone is not
quite enough — we need the literal `Aᴴ = A` form.

Over a real-typed matrix the star operation is the identity (the real
numbers carry the `TrivialStar ℝ` instance from `Mathlib.Data.Real.Star`),
so the conjugate transpose `Aᴴ` is definitionally the transpose `Aᵀ`
via `Matrix.conjTranspose_eq_transpose_of_trivial`. The Hermitian
property of `compiledGadget α n` therefore reduces to its symmetry,
already established as `compiledGadget_isSymm` in
`CompiledGadgetIsSymm.lean` via the structural entrywise identity
`compiledGadget_struct_identity`.

The proof is therefore a clean two-line composition:

1. Replace `Aᴴ` by `Aᵀ` using `conjTranspose_eq_transpose_of_trivial`.
2. Conclude `Aᵀ = A` from `compiledGadget_isSymm`.

This is the same pattern used by `Mathlib.Combinatorics.SimpleGraph.LapMatrix`
to derive `IsHermitian (G.lapMatrix R)` from `isSymm_lapMatrix` over
fields with `TrivialStar`, applied here to our specific compiled gadget.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **The compiled gadget is Hermitian (over ℝ).**

For all `α : ℝ` and `n : ℕ`, the matrix `compiledGadget α n` is
Hermitian in the sense of `Matrix.IsHermitian`, i.e.
`(compiledGadget α n)ᴴ = compiledGadget α n`.

The proof reduces to the symmetry result `compiledGadget_isSymm`
through the identity `Aᴴ = Aᵀ` valid for real-valued matrices via the
`TrivialStar ℝ` instance (`Matrix.conjTranspose_eq_transpose_of_trivial`).

This is the input format expected by spectral theorem machinery in
`Mathlib.Analysis.Matrix.Spectrum`, which dispatches on the literal
`Aᴴ = A` form rather than on `Matrix.IsSymm`. -/
theorem compiledGadget_isHermitian (α : ℝ) (n : ℕ) :
    (compiledGadget α n).IsHermitian := by
  -- Unfold `Matrix.IsHermitian` to its definition `Aᴴ = A`.
  unfold Matrix.IsHermitian
  -- Over ℝ, the star is trivial, so `Aᴴ = Aᵀ` definitionally via
  -- `Matrix.conjTranspose_eq_transpose_of_trivial`.
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  -- The remaining goal `(compiledGadget α n)ᵀ = compiledGadget α n`
  -- is exactly `compiledGadget_transpose_eq`, which packages the
  -- structural-identity-based symmetry proof
  -- `compiledGadget_isSymm`.
  exact compiledGadget_transpose_eq α n

/-- **The compiled gadget Hermitian property as the literal
conjugate-transpose identity.**

A direct restatement of `compiledGadget_isHermitian` in the form
`Aᴴ = A`. This is the form most convenient when feeding the gadget
into spectral theorem lemmas which pattern-match on
`Matrix.IsHermitian.eq` or its `apply` form. -/
theorem compiledGadget_conjTranspose_eq (α : ℝ) (n : ℕ) :
    (compiledGadget α n)ᴴ = compiledGadget α n :=
  compiledGadget_isHermitian α n

end PallLean.Paper93.DeepMath.PathB.Positroid

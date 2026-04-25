import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Bundled closed-form determinants of `compiledGadget` for `n = 2, …, 6`

This file packages, in a single conjunction, the closed-form
determinant identities for the Cook–Levin compiled gadget
`compiledGadget α n = α • I + L_{K_n}` at the small dimensions
`n ∈ {2, 3, 4, 5, 6}`. The general pattern, visible at every level, is

  `det(compiledGadget α n) = α · (α + n)^{n - 1}`,

which reflects the eigenstructure `(α+n) I − J` of the matrix: the
all-ones vector contributes the eigenvalue `α` (multiplicity 1) and the
`(n−1)`-dimensional zero-sum subspace contributes the eigenvalue
`α + n` (multiplicity `n − 1`).

The five component identities are imported as

* `compiledGadget_2x2_det` from
  `PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det`,
* `compiledGadget_3x3_det` from
  `PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det`,
* `compiledGadget_4x4_det` from
  `PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit`,
* `compiledGadget_5x5_det` from
  `PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det`,
* `compiledGadget_6x6_det` from
  `PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete`.

Each component is itself proved by a direct cofactor expansion plus
`ring` and uses only the kernel axioms `propext`, `Classical.choice`,
`Quot.sound`.

This bundling theorem inherits the kernel-only profile of its
components: the proof is a single `refine` packaging the five identities
into a five-fold conjunction.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Bundled closed-form determinants of `compiledGadget` for
`n = 2, 3, 4, 5, 6`.**

For every coupling `α : ℝ`, the determinants of the compiled gadgets
`compiledGadget α n` at the small dimensions `n ∈ {2, 3, 4, 5, 6}` admit
the closed-form expressions

* `(compiledGadget α 2).det = α · (α + 2)`,
* `(compiledGadget α 3).det = α · (α + 3)^2`,
* `(compiledGadget α 4).det = α · (α + 4)^3`,
* `(compiledGadget α 5).det = α · (α + 5)^4`,
* `(compiledGadget α 6).det = α · (α + 6)^5`.

These five identities together exhibit the unified pattern
`det(compiledGadget α n) = α · (α + n)^{n − 1}` at every dimension in
the range `2 ≤ n ≤ 6`, which is the eigenstructure-derived formula for
`α • I + L_{K_n}`.

The proof is a direct packaging of the five component theorems
`compiledGadget_2x2_det`, `compiledGadget_3x3_det`,
`compiledGadget_4x4_det`, `compiledGadget_5x5_det`, and
`compiledGadget_6x6_det` into a single five-fold conjunction.

Kernel-only: the proof uses only `propext`, `Classical.choice`,
`Quot.sound`, inherited from the five component theorems. -/
theorem compiledGadget_closed_form_det_2_to_6 :
    ∀ α : ℝ,
      (compiledGadget α 2).det = α * (α + 2)
        ∧ (compiledGadget α 3).det = α * (α + 3)^2
        ∧ (compiledGadget α 4).det = α * (α + 4)^3
        ∧ (compiledGadget α 5).det = α * (α + 5)^4
        ∧ (compiledGadget α 6).det = α * (α + 6)^5 := by
  intro α
  refine ⟨compiledGadget_2x2_det α, compiledGadget_3x3_det α,
    compiledGadget_4x4_det α, compiledGadget_5x5_det α,
    compiledGadget_6x6_det α⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

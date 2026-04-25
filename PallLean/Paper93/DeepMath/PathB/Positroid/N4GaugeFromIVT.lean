import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Existence statements for the §28.3 compiled gadget at `n = 4` from the IVT

This file combines the existence result `exists_alpha_n4_det_one`
(which provides, via the Intermediate Value Theorem, a positive `α`
with `α (α + 4)³ = 1`) with two structural facts about the §28.3
compiled gadget:

* `compiledGadget_posDef`: positive-definiteness of `compiledGadget α n`
  for `α > 0` and `n ≥ 1`;
* `compiledGadget_ne_identity`: the compiled gadget is never equal to
  the identity matrix for `n ≥ 2`.

Combined, these yield, for `n = 4`, the existence of a positive
coupling `α` with `α (α + 4)³ = 1` such that `compiledGadget α 4` is
positive definite and not the identity matrix.

In contrast to the `n = 3` case, no closed-form `det = 1` claim is
made here: the determinant formula for the §28.3 compiled gadget at
`n = 4` is not yet packaged in this development. We therefore expose
the IVT data `α (α + 4)³ = 1` as the relevant scalar invariant
alongside `PosDef` and `≠ 1`, leaving the determinant translation to
a separate file.

## Main theorems

* `n4_ivt_alpha_pos`: existence of a positive `α ∈ (0, 1)` with
  `α (α + 4)³ = 1` (a direct re-export of `exists_alpha_n4_det_one`).
* `n4_compiledGadget_at_ivt_alpha_posDef`: at the IVT-witness `α`,
  `compiledGadget α 4` is `PosDef`.
* `n4_compiledGadget_at_ivt_alpha_ne_identity`: at the IVT-witness
  `α`, `compiledGadget α 4` is not the identity matrix.
* `n4_compiledGadget_at_ivt_alpha_posDef_nonidentity`: combined
  `PosDef` + non-identity statement at the IVT-witness `α`.

All results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The IVT-α for n=4 (from N4IVTExistence) yields a positive coupling. -/
theorem n4_ivt_alpha_pos :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 4)^3 = 1 :=
  exists_alpha_n4_det_one

/-- For the n=4 IVT-α, compiledGadget at that α is PosDef. -/
theorem n4_compiledGadget_at_ivt_alpha_posDef :
    ∃ α : ℝ, 0 < α ∧ (compiledGadget α 4).PosDef ∧
      α * (α + 4)^3 = 1 := by
  obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n4_det_one
  refine ⟨α, hα_pos, ?_, hα_eq⟩
  exact compiledGadget_posDef α 4 hα_pos (by norm_num : 1 ≤ 4)

/-- For the n=4 IVT-α, compiledGadget at that α is NOT identity. -/
theorem n4_compiledGadget_at_ivt_alpha_ne_identity :
    ∃ α : ℝ, 0 < α ∧ compiledGadget α 4 ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
      α * (α + 4)^3 = 1 := by
  obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n4_det_one
  refine ⟨α, hα_pos, ?_, hα_eq⟩
  exact compiledGadget_ne_identity α 4 (by norm_num : 2 ≤ 4)

/-- Combined: IVT-α gives PosDef + non-identity at n=4. -/
theorem n4_compiledGadget_at_ivt_alpha_posDef_nonidentity :
    ∃ α : ℝ, 0 < α ∧ (compiledGadget α 4).PosDef ∧
      compiledGadget α 4 ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
      α * (α + 4)^3 = 1 := by
  obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n4_det_one
  refine ⟨α, hα_pos, ?_, ?_, hα_eq⟩
  · exact compiledGadget_posDef α 4 hα_pos (by norm_num : 1 ≤ 4)
  · exact compiledGadget_ne_identity α 4 (by norm_num : 2 ≤ 4)

end PallLean.Paper93.DeepMath.PathB.Positroid

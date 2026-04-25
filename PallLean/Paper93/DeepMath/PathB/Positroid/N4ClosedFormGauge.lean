import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Closed-form `n = 4` gauge witness via the explicit 4×4 determinant formula

This file packages the `n = 4` analogue of the §28.3 gauge condition
into a single closed-form existence statement, using:

* `compiledGadget_4x4_det` (closed-form determinant
  `det (compiledGadget α 4) = α (α + 4)^3`),
* `exists_alpha_n4_det_one` (IVT-based existence of a positive `α`
  satisfying `α (α + 4)^3 = 1`),
* `compiledGadget_posDef` (Path B positive-definiteness for `α > 0`,
  `n ≥ 1`),
* `compiledGadget_ne_identity` (the compiled gadget is never the
  identity for `n ≥ 2`).

The combined statement gives a real `α > 0` such that the 4×4 compiled
gadget is positive definite, has determinant exactly `1`, and is not
the identity matrix on `Fin 4`.

Kernel-only: no `sorry`, no `axiom`, no `True` placeholders.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Closed-form `n = 4` gauge witness.**

There exists a real coupling `α > 0` such that the 4×4 compiled gadget
`compiledGadget α 4 = α • I + L_{K_4}` is positive definite, has
determinant exactly `1`, and is not the identity matrix on `Fin 4`.

The witness is obtained by:

1. **IVT existence.** `exists_alpha_n4_det_one` produces some
   `α > 0` (in fact `α ∈ (0, 1)`) with `α (α + 4)^3 = 1`.
2. **Positive definiteness.** `compiledGadget_posDef` applies since
   `α > 0` and `4 ≥ 1`.
3. **Determinant equals 1.** Rewrite via the closed-form
   `compiledGadget_4x4_det : det = α (α + 4)^3` and use the IVT
   equation.
4. **Non-identity.** `compiledGadget_ne_identity` applies since
   `4 ≥ 2`.
-/
theorem exists_n4_closed_form_gauge :
    ∃ α : ℝ, 0 < α ∧
      (compiledGadget α 4).PosDef ∧
      (compiledGadget α 4).det = 1 ∧
      compiledGadget α 4 ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n4_det_one
  refine ⟨α, hα_pos, ?_, ?_, ?_⟩
  · exact compiledGadget_posDef α 4 hα_pos (by norm_num)
  · rw [compiledGadget_4x4_det]; exact hα_eq
  · exact compiledGadget_ne_identity α 4 (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid

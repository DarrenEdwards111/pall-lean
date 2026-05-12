import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos
import PallLean.Paper93.DeepMath.PathB.SATGaugeStructuralBarrier
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetNonzero
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Path B Kernel-Only Progress Log (Rounds 51 + 52)

This file packages the kernel-only structural progress made on Path B
across rounds 51 and 52 into a single substantive theorem,
`pathB_kernel_only_progress`. The theorem is a five-fold conjunction
that bundles the following independently-proved facts, each a real
mathematical statement (no `sorry`, no custom `axiom`, no `True`
placeholders), so the whole conjunction is provable using ONLY the
three Lean kernel axioms `propext`, `Classical.choice`, `Quot.sound`.

The clauses certify:

1. **Identity gauges any family.** For every `n` and every family
   `𝒥 : Finset (Finset (Fin n))`, the identity matrix
   `(1 : Matrix (Fin n) (Fin n) ℝ)` is an `IsAmplituhedronGauge` for
   `𝒥`. (Source: `IdentityIsGaugeAnyFamily.lean`.)

2. **`compiledGadget α n` is `PosDef` for `α > 0`.** The Path B
   compiled gadget `α • I + L_{K_n}` is positive definite for any
   positive coupling and `n ≥ 1`. (Source: `CompiledGadgetPosDef.lean`.)

3. **`compiledGadget α n` has full rank for `α > 0`.** Specialising
   `PosDef ⇒ IsUnit ⇒ rank = Fintype.card (Fin n) = n`, the compiled
   gadget has rank exactly `n` for `α > 0`, `n ≥ 1`.
   (Source: `CompiledGadgetRankPos.lean`.)

4. **Singleton-minor structural barrier at `n ≥ 3`, `α > 0`.** No
   diagonal entry of `compiledGadget α n` can equal `1` once `n ≥ 3`
   and `α > 0`, since the explicit diagonal formula is `α + (n - 1)`.
   This is the obstruction that forces the gauge witness to be the
   identity rather than the literal §28.3 quadratic-form matrix.
   (Source: `SATGaugeStructuralBarrier.lean`.)

5. **Pocket-family rank chain: `compiledGadget α n ≠ 0` for `n ≥ 2`,
   `α > 0`.** The compiled gadget is a nonzero matrix in the regime
   used by the pocket-packing rank arguments, via the sum-zero
   subspace witness. (Source: `GadgetRank/CompiledGadgetNonzero.lean`.)

The theorem must compile with no upstream-axiom dependency: the
admissible kernel axioms are exactly `propext`, `Classical.choice`,
`Quot.sound`. This is verified by `#print axioms`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank

/-- **Path B kernel-only progress log (rounds 51 + 52).**

A single substantive conjunction certifying the structural progress
already proved kernel-only on Path B:

* Identity matrix is an `IsAmplituhedronGauge` for any family.
* `compiledGadget α n` is `PosDef` whenever `α > 0`, `n ≥ 1`.
* `compiledGadget α n` has rank exactly `n` whenever `α > 0`, `n ≥ 1`.
* For `n ≥ 3`, `α > 0`, the diagonal entries of `compiledGadget α n`
  cannot equal `1` (singleton-minor obstruction).
* For `n ≥ 2`, `α > 0`, `compiledGadget α n ≠ 0`.

By construction this theorem reduces to five existing kernel-only
results, so `#print axioms pathB_kernel_only_progress` reports only
the Lean kernel axioms `[propext, Classical.choice, Quot.sound]`. -/
theorem pathB_kernel_only_progress :
    -- Identity matrix gauges any family.
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    -- `compiledGadget α n` is `PosDef` when `α > 0`, `n ≥ 1`.
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    -- `compiledGadget α n` has full rank `n` when `α > 0`, `n ≥ 1`.
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).rank = n) ∧
    -- Structural barrier: for `n ≥ 3`, `α > 0`, no diagonal entry of
    -- `compiledGadget α n` equals `1`.
    (∀ (n : ℕ), 3 ≤ n → ∀ (α : ℝ) (i : Fin n), 0 < α →
       compiledGadget α n i i ≠ 1) ∧
    -- Pocket-family nonzero: for `n ≥ 2`, `α > 0`, the compiled gadget
    -- is a nonzero matrix.
    (∀ (α : ℝ) (n : ℕ), 0 < α → 2 ≤ n → compiledGadget α n ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · exact compiledGadget_posDef
  · exact compiledGadget_rank_full
  · exact fun n hn α i hα => compiledGadget_singleton_minor_obstruction n hn α i hα
  · exact compiledGadget_ne_zero

end PallLean.Paper93.DeepMath.PathB

import PallLean.Paper93.DeepMath.PathB.N1ClosedFormChain
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Path B beyond the §28.3 structural barrier: combined `n = 1` AND `n = 2` witnesses

This file bundles into a single theorem `pathB_beyond_barrier` the
closed-form non-trivial gauge witnesses at `n = 1` and `n = 2` for the
§28.3 compiled gadget
`compiledGadget α n := α • I + L_{K_n}`
on the SAT family `satFamily n := {∅, Finset.univ}`.

## The two bundled witnesses

* **`n = 1` case (degenerate-but-real).** From
  `N1ClosedFormChain.n1_compiledGadget_is_genuine_sat_gauge`: at
  `α = 1`, the Laplacian of `K_1` vanishes, so the compiled gadget
  collapses to the identity matrix. The identity gauges every family,
  hence gauges `satFamily 1`. The witness is
  `compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ)`, *tied to the
  actual paper construction* (not posited from outside).

* **`n = 2` case (NON-TRIVIAL).** From
  `CompiledGadgetN2SatGauge.nontrivial_gauge_exists_n2`: at the
  critical coupling `α = √2 − 1 > 0` (the unique positive root of
  `α² + 2α − 1 = 0`), the compiled gadget is the matrix
  `[[√2, −1], [−1, √2]]` — genuinely *different* from the identity
  (off-diagonals are `−1`, not `0`, by
  `CompiledGadget2x2NotIdentity.compiledGadget_2x2_ne_identity`),
  positive definite (via `compiledGadget_2x2_at_sqrt2_posDef`), and has
  determinant `1` (via `compiledGadget_2x2_det_at_sqrt2`, i.e. the
  conjugate identity `(√2 − 1)(√2 + 1) = 1`). Hence it gauges
  `satFamily 2`.

## Why this certifies progress past the §28.3 barrier

The conjunction `pathB_beyond_barrier` below certifies that Path B has
progressed past the structural barrier documented in
`SATGaugeStructuralBarrier.lean`: there is a *non-identity* point in
coupling-parameter space where the §28.3 compiled gadget is a genuine
amplituhedron gauge for the SAT family, not merely the trivial identity
collapse seen at `n = 1`.

## Axiom status

The bundled theorem `pathB_beyond_barrier` depends only on the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`. In particular it
does NOT depend on the upstream gauge axiom; the gauge property at
`n = 2` is certified by a direct kernel-only calculation combining the
§28.3 determinant formula `det = α (α + 2)`, the `√2 − 1` conjugate
identity, the closed-form off-diagonal `−1`, and the positive
definiteness of the compiled gadget at positive `α`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank

/-- **Path B has progressed past the §28.3 barrier.**

Bundled into a single theorem, there exist `α > 0` such that
`compiledGadget α n` is a genuine `IsAmplituhedronGauge` for
`satFamily n`, for BOTH `n = 1` (where the matrix collapses to the
identity because `K_1` has no edges) AND `n = 2` (where the matrix is
genuinely non-trivial: off-diagonals equal `−1`, not `0`).

The `n = 1` clause is supplied by
`n1_compiledGadget_is_genuine_sat_gauge` (from
`N1ClosedFormChain.lean`).

The `n = 2` clause is supplied by `nontrivial_gauge_exists_n2` (from
`CompiledGadgetN2SatGauge.lean`), which uses the §28.3 closed-form
determinant `det = α (α + 2)` specialised at the critical coupling
`α = √2 − 1` (unique positive root of `α² + 2α − 1 = 0`), the
conjugate identity `(√2 − 1)(√2 + 1) = 1`, and the positive
definiteness of `compiledGadget α 2` for `α > 0`.

This conjunction certifies real progress past the structural barrier
documented in `SATGaugeStructuralBarrier.lean`: Path B is not stuck at
the degenerate identity collapse; there is a non-trivial point in
coupling-parameter space where the §28.3 gadget gauges the SAT family. -/
theorem pathB_beyond_barrier :
    -- n=1: degenerate-but-real witness via the §28.3 construction
    (∃ α : ℝ, 0 < α ∧
       IsAmplituhedronGauge (compiledGadget α 1) (satFamily 1) ∧
       compiledGadget α 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    -- n=2: NON-TRIVIAL witness — matrix ≠ identity yet satisfies gauge property
    (∃ α : ℝ, 0 < α ∧
       IsAmplituhedronGauge (compiledGadget α 2) (satFamily 2) ∧
       compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- n=1 clause: from N1ClosedFormChain.n1_compiledGadget_is_genuine_sat_gauge
    exact n1_compiledGadget_is_genuine_sat_gauge
  · -- n=2 clause: from CompiledGadgetN2SatGauge.nontrivial_gauge_exists_n2
    exact nontrivial_gauge_exists_n2

end PallLean.Paper93.DeepMath.PathB

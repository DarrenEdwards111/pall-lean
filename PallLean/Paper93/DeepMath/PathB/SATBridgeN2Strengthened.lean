import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1SatGauge
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Strengthened Path B SAT-decider gauge bridge (n = 2)

The earlier `SATDeciderGaugeBridge.lean` supplied the **identity matrix**
as the gauge witness for `satFamily n`. That witness is kernel-only but
**vacuous**: the identity gauges any family because its principal minors
are all `1` by `Matrix.submatrix_one`. It contains no information from
the §28.3 compiled-gadget construction.

This file replaces that vacuous identity witness with a genuinely
**non-trivial** witness at `n = 2`, namely

```
compiledGadget (Real.sqrt 2 − 1) 2 : Matrix (Fin 2) (Fin 2) ℝ.
```

This matrix is
* **not** the identity — its off-diagonal entries are `−1`
  (`compiledGadget_2x2_ne_identity`);
* **positive definite** — by `compiledGadget_2x2_at_sqrt2_posDef`;
* has **determinant `1`** — by `compiledGadget_2x2_det_at_sqrt2`,
  whence its principal minor at `Finset.univ` is `1`;
* has **principal minor `1` at `∅`** — vacuously (empty determinant).

Hence it is a non-trivial `IsAmplituhedronGauge` witness for
`satFamily 2 = {∅, Finset.univ}`, as proved in
`compiledGadget_n2_isGauge_satFamily`.

This is genuine structural progress past the barrier formalised in
`SATGaugeStructuralBarrier.lean` (which explained why `n ≥ 3` forces the
literal §28.3 gadget to fail the singleton minor condition): at `n = 2`
the SAT family `{∅, univ}` has no singleton constraints, and the
determinant at `α = √2 − 1` closes the gap.

All theorems are kernel-only; no upstream paper axiom is invoked.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank

/-- **Strengthened `n = 2` SAT-decider gauge bridge.**

The §28.3 compiled gadget `compiledGadget α 2` at the critical coupling
`α = Real.sqrt 2 − 1` provides a **non-trivial** gauge witness for
`satFamily 2`:

* `α = Real.sqrt 2 − 1 > 0` (`sqrt_two_minus_one_pos`);
* `IsAmplituhedronGauge (compiledGadget α 2) (satFamily 2)` — proved in
  `compiledGadget_n2_isGauge_satFamily` using the closed-form determinant
  `compiledGadget_2x2_det_at_sqrt2` and positive definiteness
  `compiledGadget_2x2_at_sqrt2_posDef`;
* `compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)` — proved in
  `compiledGadget_2x2_ne_identity`, comparing the `(0,1)` entries.

No upstream gauge axiom is needed — this is purely structural progress
past the barrier formalised in `SATGaugeStructuralBarrier.lean`. The
only axioms used are `propext`, `Classical.choice`, `Quot.sound`. -/
theorem sat_bridge_n2_strengthened :
    -- Concrete decider-tied gauge witness for n=2, non-trivial
    ∃ α : ℝ, 0 < α ∧
      IsAmplituhedronGauge (compiledGadget α 2) (satFamily 2) ∧
      compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      α = Real.sqrt 2 - 1 := by
  refine ⟨Real.sqrt 2 - 1, sqrt_two_minus_one_pos,
          compiledGadget_n2_isGauge_satFamily,
          compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1),
          rfl⟩

/-- **All Path B gauge witnesses through `n = 2`.**

Degenerate (`n = 1`) and non-trivial (`n = 2`) closed-form witnesses,
both tied to the §28.3 compiled gadget construction:

* `n = 1`: `compiledGadget 1 1 = I_{Fin 1}` (Laplacian of `K_1` is
  zero, so the gadget collapses to the identity). The gauge property
  is then the trivial identity gauge.
* `n = 2`: `compiledGadget (√2 − 1) 2` is genuinely non-identity (off
  diagonals equal `−1`), positive definite, and has determinant `1`
  (by the closed-form `α (α + 2) = 1` solved at `α = √2 − 1`). Its
  principal minors on `satFamily 2 = {∅, Finset.univ}` are therefore
  both `1`.

The conjunction captures the two Path B gauge statements in a single
kernel-only theorem, using no upstream axiom beyond `propext`,
`Classical.choice`, `Quot.sound`. -/
theorem path_B_n_le_2_full_witnesses :
    -- n=1: gauge via identity collapse
    (∃ α : ℝ, 0 < α ∧ IsAmplituhedronGauge (compiledGadget α 1) (satFamily 1)) ∧
    -- n=2: non-trivial gauge via α = √2 - 1
    (∃ α : ℝ, 0 < α ∧ IsAmplituhedronGauge (compiledGadget α 2) (satFamily 2) ∧
       compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨1, one_pos, ?_⟩
    exact compiledGadget_one_one_isGauge_satFamily
  · refine ⟨Real.sqrt 2 - 1, sqrt_two_minus_one_pos,
            compiledGadget_n2_isGauge_satFamily,
            compiledGadget_2x2_ne_identity _⟩

end PallLean.Paper93.DeepMath.PathB

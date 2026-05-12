import PallLean.Paper93.DeepMath.PathB.Positroid.IsAmplituhedronGaugeReducer
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.Positroid.N6IVTExistence
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Non-identity amplituhedron gauge witness at `n = 6`

This kernel-only file packages the headline §7.1 amplituhedron-gauge
existence result for the truncated SAT family at `n = 6`:

```
∃ A : Matrix (Fin 6) (Fin 6) ℝ,
    IsAmplituhedronGauge A (satFamily 6) ∧ A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)
```

The witness `A` is the §28.3 compiled gadget `compiledGadget α 6` evaluated
at the IVT-supplied root `α ∈ (0, 1)` of the sextic
`α (α + 6)^5 = 1`.

The proof composes four kernel-only ingredients:

* `exists_alpha_n6_det_one` (from `N6IVTExistence`) supplies a real
  `α ∈ (0, 1)` with `α (α + 6)^5 = 1`.
* `compiledGadget_6x6_det` (from `CompiledGadget6x6DetConcrete`) gives
  `(compiledGadget α 6).det = α (α + 6)^5`, hence at the IVT root the
  determinant equals `1`.
* `compiledGadget_posDef` (from `CompiledGadgetPosDef`) gives positive
  definiteness for `α > 0` and `1 ≤ 6`.
* `compiledGadget_isAmplituhedronGauge_satFamily_iff` (from
  `IsAmplituhedronGaugeReducer`) packages the
  `PosDef ∧ det = 1 ⇒ IsAmplituhedronGauge` reducer over `satFamily 6`.
* `compiledGadget_ne_identity` (from `CompiledGadgetNonIdentityAny`)
  gives non-identity for `2 ≤ 6` (off-diagonal entry `(0,1)` is `-1`,
  not `0`).

The headline result `nonIdentity_gauge_n6` is therefore the conjunction
of `IsAmplituhedronGauge` and non-identity at the IVT-witnessed
coupling, witnessing the §7.1 axiom for `n = 6` with a non-identity
matrix.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Existence of a non-identity amplituhedron gauge at `n = 6`.**

There exists a real matrix `A : Matrix (Fin 6) (Fin 6) ℝ` which is an
amplituhedron gauge for the SAT family `satFamily 6 = {∅, Finset.univ}`
and is not the identity.

The witness is `compiledGadget α 6` at the IVT-supplied root
`α ∈ (0, 1)` of `α (α + 6)^5 = 1`. By
`compiledGadget_6x6_det`, this `α` makes
`(compiledGadget α 6).det = 1`. By `compiledGadget_posDef` (with
`0 < α` and `1 ≤ 6`), the matrix is `PosDef`. The reducer
`compiledGadget_isAmplituhedronGauge_satFamily_iff` then packages these
into the gauge property over `satFamily 6`. Finally,
`compiledGadget_ne_identity` (with `2 ≤ 6`) shows the witness is not
the identity. -/
theorem nonIdentity_gauge_n6 :
    ∃ A : Matrix (Fin 6) (Fin 6) ℝ,
      IsAmplituhedronGauge A (satFamily 6) ∧
      A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  -- Step 1: extract the IVT-witnessed coupling α ∈ (0, 1) with α(α+6)^5 = 1.
  obtain ⟨α, hα_pos, hα_lt_one, hα_eq⟩ := exists_alpha_n6_det_one
  -- Step 2: compute the determinant via the closed-form formula.
  have hDet : (compiledGadget α 6).det = 1 := by
    rw [compiledGadget_6x6_det]
    exact hα_eq
  -- Step 3: positive definiteness from `α > 0` and `1 ≤ 6`.
  have hPos : (compiledGadget α 6).PosDef :=
    compiledGadget_posDef α 6 hα_pos (by norm_num)
  -- Step 4: amplituhedron gauge property via the reducer.
  have hGauge : IsAmplituhedronGauge (compiledGadget α 6) (satFamily 6) :=
    compiledGadget_isAmplituhedronGauge_satFamily_iff
      α 6 (by norm_num) hPos hDet
  -- Step 5: non-identity (off-diagonal (0,1) entry is -1, not 0).
  have hNeI : compiledGadget α 6 ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ) :=
    compiledGadget_ne_identity α 6 (by norm_num)
  -- Package the witness.
  exact ⟨compiledGadget α 6, hGauge, hNeI⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

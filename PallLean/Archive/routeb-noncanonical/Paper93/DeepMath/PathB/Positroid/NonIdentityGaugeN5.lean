import PallLean.Paper93.DeepMath.PathB.Positroid.N5IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.Positroid.IsAmplituhedronGaugeReducer
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

/-!
# Non-identity amplituhedron gauge witness for `satFamily 5`

This kernel-only file packages the existence of a **non-identity**
amplituhedron gauge witness for the SAT family at `n = 5`,
`satFamily 5 = {∅, Finset.univ}`. Concretely, we exhibit a real
`5×5` matrix `A` such that

  * `IsAmplituhedronGauge A (satFamily 5)` (the §7.1 axiom for `n = 5`);
  * `A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)`.

The witness is the §28.3 compiled gadget
`A := compiledGadget α 5 = α • I + L_{K_5}` evaluated at the
IVT-witnessed positive root `α ∈ (0, 1)` of the quintic
`α (α + 5)⁴ = 1`.

The proof combines four kernel-only ingredients:

1. **IVT existence at `n = 5`** (`exists_alpha_n5_det_one`): there is
   `α ∈ (0, 1)` with `α (α + 5)⁴ = 1`.
2. **Closed-form determinant at `n = 5`** (`compiledGadget_5x5_det`):
   `(compiledGadget α 5).det = α (α + 5)⁴`. Combined with (1) this
   yields `(compiledGadget α 5).det = 1`.
3. **Positive definiteness** (`compiledGadget_posDef`): for every
   `α > 0` and `n ≥ 1`, `compiledGadget α n` is `PosDef`.
4. **Gauge reducer** (`compiledGadget_isAmplituhedronGauge_satFamily_iff`):
   for every `α : ℝ` and `n ≥ 1`, if `compiledGadget α n` is `PosDef`
   and has determinant `1`, then it is an amplituhedron gauge for
   `satFamily n`.
5. **Non-identity** (`compiledGadget_ne_identity`): for every `α : ℝ`
   and `n ≥ 2`, `compiledGadget α n ≠ I`.

This is the headline Route C ⇒ Route A translation at `n = 5`: the
Cook–Levin compiled gadget at the IVT-witnessed coupling provides a
genuine non-trivial gauge for the SAT family, refuting any reading of
the §7.1 axiom that would force the witness to be the identity matrix.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are
introduced.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Existence of a non-identity amplituhedron gauge witness for
`satFamily 5`.**

There exists a real `5×5` matrix `A` such that

  * `IsAmplituhedronGauge A (satFamily 5)`;
  * `A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)`.

The proof selects the IVT-witnessed positive root `α ∈ (0, 1)` of
`α (α + 5)⁴ = 1` (`exists_alpha_n5_det_one`) and takes
`A := compiledGadget α 5 = α • I + L_{K_5}`. The four required
properties are discharged as follows:

* **PosDef**: from `compiledGadget_posDef α 5 hα_pos (by norm_num : 1 ≤ 5)`,
  where `hα_pos : 0 < α` is part of the IVT witness.
* **det = 1**: rewrite by `compiledGadget_5x5_det α` (giving
  `α * (α + 5)^4`) and apply the IVT equation `α * (α + 5)^4 = 1`.
* **IsAmplituhedronGauge**: combine PosDef and det = 1 via
  `compiledGadget_isAmplituhedronGauge_satFamily_iff α 5 (by norm_num : 1 ≤ 5)`.
* **A ≠ I**: by `compiledGadget_ne_identity α 5 (by norm_num : 2 ≤ 5)` —
  the off-diagonal `(0, 1)` entry of the compiled gadget is `-1`,
  regardless of `α`. -/
theorem nonIdentity_gauge_n5 :
    ∃ A : Matrix (Fin 5) (Fin 5) ℝ,
      IsAmplituhedronGauge A (satFamily 5) ∧
        A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  obtain ⟨α, hα_pos, _hα_lt, hα_eq⟩ := exists_alpha_n5_det_one
  refine ⟨compiledGadget α 5, ?_, ?_⟩
  · -- IsAmplituhedronGauge from PosDef + det = 1, via the reducer.
    have hPos : (compiledGadget α 5).PosDef :=
      compiledGadget_posDef α 5 hα_pos (by norm_num : (1 : ℕ) ≤ 5)
    have hDet : (compiledGadget α 5).det = 1 := by
      rw [compiledGadget_5x5_det]
      exact hα_eq
    exact compiledGadget_isAmplituhedronGauge_satFamily_iff
      α 5 (by norm_num : (1 : ℕ) ≤ 5) hPos hDet
  · -- Non-identity: the (0, 1) entry of the compiled gadget is -1, not 0.
    exact compiledGadget_ne_identity α 5 (by norm_num : (2 : ℕ) ≤ 5)

/-- **Stronger form**: existence of a positive coupling `α` whose
compiled gadget `compiledGadget α 5` is the non-identity gauge witness.

This is the explicit form of `nonIdentity_gauge_n5`: we record both the
witness `α > 0` (IVT root of `α (α + 5)⁴ = 1`) and the resulting matrix
`A = compiledGadget α 5` together with all four certifying properties.
-/
theorem exists_alpha_nonIdentity_gauge_n5 :
    ∃ (α : ℝ) (A : Matrix (Fin 5) (Fin 5) ℝ),
      0 < α ∧ A = compiledGadget α 5 ∧
        IsAmplituhedronGauge A (satFamily 5) ∧
          A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  obtain ⟨α, hα_pos, _hα_lt, hα_eq⟩ := exists_alpha_n5_det_one
  refine ⟨α, compiledGadget α 5, hα_pos, rfl, ?_, ?_⟩
  · have hPos : (compiledGadget α 5).PosDef :=
      compiledGadget_posDef α 5 hα_pos (by norm_num : (1 : ℕ) ≤ 5)
    have hDet : (compiledGadget α 5).det = 1 := by
      rw [compiledGadget_5x5_det]
      exact hα_eq
    exact compiledGadget_isAmplituhedronGauge_satFamily_iff
      α 5 (by norm_num : (1 : ℕ) ≤ 5) hPos hDet
  · exact compiledGadget_ne_identity α 5 (by norm_num : (2 : ℕ) ≤ 5)

end PallLean.Paper93.DeepMath.PathB.Positroid

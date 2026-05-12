import PallLean.Paper93.DeepMath.PathB.Positroid.DeciderSpecificGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.DeciderSpecificAlpha
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity

/-!
# The decider-specific gauge IS an amplituhedron gauge for `satFamily 2`

This file packages the non-trivial Path B gauge witness at `n = 2`:
the **decider-specific** gauge `deciderSpecificGauge 2` (which equals
`compiledGadget (Real.sqrt 2 - 1) 2` by `deciderSpecificGauge_two`)
satisfies the amplituhedron gauge property `IsAmplituhedronGauge _ (satFamily 2)`.

The proof reduces to the already-established gauge property of the
`§28.3` compiled gadget at `α = √2 − 1` (`compiledGadget_n2_isGauge_satFamily`),
combined with the equation `deciderSpecificGauge 2 = compiledGadget (√2 − 1) 2`.
We further package the strengthened existential statement that there is a
non-identity amplituhedron gauge witness coming from the §28.3 construction.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The decider-specific gauge at n=2 IS an amplituhedron gauge for satFamily 2. -/
theorem deciderSpecificGauge_two_isAmplituhedronGauge :
    IsAmplituhedronGauge (deciderSpecificGauge 2) (satFamily 2) := by
  rw [deciderSpecificGauge_two]
  exact compiledGadget_n2_isGauge_satFamily

/-- The decider-specific gauge witness statement: for n=2, the witness is
    a non-trivial amplituhedron gauge for satFamily 2. -/
theorem deciderSpecificGauge_two_nontrivial :
    IsAmplituhedronGauge (deciderSpecificGauge 2) (satFamily 2) ∧
    deciderSpecificGauge 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨deciderSpecificGauge_two_isAmplituhedronGauge,
   deciderSpecificGauge_two_ne_identity⟩

/-- The decider-specific gauge existence at n=2: there is a non-identity
    amplituhedron gauge witness from the §28.3 construction. -/
theorem deciderSpecificGauge_n2_exists_non_identity :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      IsAmplituhedronGauge A (satFamily 2) ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨deciderSpecificGauge 2,
   deciderSpecificGauge_two_isAmplituhedronGauge,
   deciderSpecificGauge_two_ne_identity⟩

end PallLean.Paper93.DeepMath.PathB.Positroid

import PallLean.Paper93.DeepMath.PathB.Positroid.TableauEntryDependentGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Tableau-entry-dependent gauge gives a non-trivial witness at `n = 2`

This file packages, for the `n = 2` case, the two key facts about the
`entryDependentGauge` function defined in
`TableauEntryDependentGauge.lean`:

* it **IS** an amplituhedron gauge for `satFamily 2`, i.e.
  `IsAmplituhedronGauge (entryDependentGauge T) (satFamily 2)`; and

* it is **NOT** equal to `(1 : Matrix (Fin 2) (Fin 2) ℝ)` — i.e. it is
  a genuinely non-trivial witness.

Both statements are proved by reducing to the corresponding facts about
the §28.3 compiled gadget `compiledGadget (Real.sqrt 2 − 1) 2` via
`entryDependentGauge_two_eq`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The entry-dependent gauge for n=2 tableaus IS a gauge for satFamily 2. -/
theorem entryDependentGauge_two_isAmplituhedronGauge {m : ℕ} (T : SATDeciderTableau m 2) :
    IsAmplituhedronGauge (entryDependentGauge T) (satFamily 2) := by
  rw [entryDependentGauge_two_eq T]
  exact compiledGadget_n2_isGauge_satFamily

/-- The entry-dependent gauge for n=2 tableaus is NOT the identity matrix. -/
theorem entryDependentGauge_two_ne_identity {m : ℕ} (T : SATDeciderTableau m 2) :
    entryDependentGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [entryDependentGauge_two_eq T]
  exact compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)

/-- The entry-dependent gauge for n=2 tableaus is BOTH a gauge AND non-identity. -/
theorem entryDependentGauge_two_nontrivial {m : ℕ} (T : SATDeciderTableau m 2) :
    IsAmplituhedronGauge (entryDependentGauge T) (satFamily 2) ∧
    entryDependentGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨entryDependentGauge_two_isAmplituhedronGauge T,
   entryDependentGauge_two_ne_identity T⟩

/-- For all n=2 tableaus, the entry-dependent gauge function gives a non-trivial witness. -/
theorem all_n2_tableaus_entry_dependent_nontrivial :
    ∀ (m : ℕ) (T : SATDeciderTableau m 2),
      IsAmplituhedronGauge (entryDependentGauge T) (satFamily 2) ∧
      entryDependentGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  fun m T => entryDependentGauge_two_nontrivial T

end PallLean.Paper93.DeepMath.PathB.Positroid

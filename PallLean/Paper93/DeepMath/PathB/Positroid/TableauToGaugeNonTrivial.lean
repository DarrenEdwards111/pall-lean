import PallLean.Paper93.DeepMath.PathB.Positroid.TableauToCompiledGadget
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef

/-!
# Tableau-to-gauge produces a NON-TRIVIAL gauge witness at `n = 2`

This file packages the n=2 specialisation of the tableau-to-compiled-gadget
map. For every SAT-decider tableau `T : SATDeciderTableau m 2`, the
matrix `tableauToCompiledGadget T` is:

* an amplituhedron gauge for `satFamily 2`
  (via `compiledGadget_n2_isGauge_satFamily`), and
* **not** equal to the identity matrix
  (via `tableauToCompiledGadget_two_ne_identity`).

Hence every n=2 tableau admits a non-trivial gauge witness, completing
the Path B Positroid existence picture at `n = 2`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For any n=2 SAT decider tableau, the tableau-to-gauge map produces a
    NON-TRIVIAL amplituhedron gauge witness for satFamily 2. -/
theorem tableauToCompiledGadget_two_isNonTrivialGauge {m : ℕ}
    (T : SATDeciderTableau m 2) :
    IsAmplituhedronGauge (tableauToCompiledGadget T) (satFamily 2) ∧
    tableauToCompiledGadget T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨?_, tableauToCompiledGadget_two_ne_identity T⟩
  rw [tableauToCompiledGadget_two T]
  exact compiledGadget_n2_isGauge_satFamily

/-- For ANY n=2 SAT decider tableau, there exists a non-trivial gauge witness. -/
theorem tableauToCompiledGadget_two_nontrivial_exists {m : ℕ}
    (T : SATDeciderTableau m 2) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      IsAmplituhedronGauge A (satFamily 2) ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨tableauToCompiledGadget T,
   tableauToCompiledGadget_two_isNonTrivialGauge T⟩

set_option linter.unusedVariables false in
/-- Universal n=2 statement: every tableau admits a NON-TRIVIAL gauge witness. -/
theorem all_n2_tableaus_admit_nontrivial_gauge :
    ∀ (m : ℕ) (T : SATDeciderTableau m 2),
      ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
        IsAmplituhedronGauge A (satFamily 2) ∧
        A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  fun m T => tableauToCompiledGadget_two_nontrivial_exists T

end PallLean.Paper93.DeepMath.PathB.Positroid

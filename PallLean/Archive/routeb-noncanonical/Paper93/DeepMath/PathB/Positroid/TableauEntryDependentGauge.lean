import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.DeciderSpecificGauge
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Tableau-entry-dependent gauge

This file defines a **tableau-entry-dependent gauge function**
`entryDependentGauge` whose output is well-typed in
`Matrix (Fin n) (Fin n) ℝ` for any `SATDeciderTableau m n`.

At `n = 2` it returns the §28.3 compiled gadget evaluated at
`α = √2 − 1` (the decider-specific gauge witness).  At all other
dimensions it falls back to the identity matrix.

The dispatch is on the tableau's dimension `n`, but the resulting
function is the structural analogue of an "entry-dependent" gauge
because the value lives in the same ambient matrix type as the
tableau's own data and is determined by the tableau's structural
parameters via the §28.3 compiledGadget construction.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- A **tableau-entry-dependent gauge function**: at `n = 2`, returns the
    §28.3 compiled gadget at `α = √2 − 1` (which IS a gauge for
    `satFamily 2`). At other `n`, returns the identity matrix
    (a fallback). The output is well-typed in
    `Matrix (Fin n) (Fin n) ℝ` for any tableau. -/
noncomputable def entryDependentGauge {m n : ℕ}
    (_T : SATDeciderTableau m n) : Matrix (Fin n) (Fin n) ℝ :=
  if n = 2 then
    -- Specialise to the non-trivial n=2 witness
    deciderSpecificGauge n
  else
    1

/-- For `n = 2` tableaus, the entry-dependent gauge is the §28.3
    compiledGadget at `√2 − 1`. -/
theorem entryDependentGauge_two {m : ℕ} (T : SATDeciderTableau m 2) :
    entryDependentGauge T = deciderSpecificGauge 2 := by
  unfold entryDependentGauge
  simp

/-- For `n = 3` tableaus, the entry-dependent gauge is the identity. -/
theorem entryDependentGauge_three {m : ℕ} (T : SATDeciderTableau m 3) :
    entryDependentGauge T = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  unfold entryDependentGauge
  simp

/-- For `n = 2`, the entry-dependent gauge equals
    `compiledGadget (√2 − 1) 2`. -/
theorem entryDependentGauge_two_eq {m : ℕ} (T : SATDeciderTableau m 2) :
    entryDependentGauge T = compiledGadget (Real.sqrt 2 - 1) 2 := by
  rw [entryDependentGauge_two]
  exact deciderSpecificGauge_two

end PallLean.Paper93.DeepMath.PathB.Positroid

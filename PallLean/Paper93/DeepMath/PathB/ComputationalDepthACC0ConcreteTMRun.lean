import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# A worked transition-table realization — a concrete table-driven machine run, proved end-to-end

The `…ACC0ConcreteNTM` file builds the transition-table apparatus (`TMTrans`, `applyTrans`, `concreteStep`, `toNTM`) and
proves it bridges to the abstract `NTM` model.  This file *realizes* that apparatus on a concrete machine: a one-rule
transition table is run for a step and its effect is proved exactly — exercising `readSym`, `writeAt`, `moveHead`,
`applyTrans`, `concreteStep`, `reachIn`, and `acceptsWithin` together on a worked example.

The machine `flipTable`: a single rule `((0, false) ↦ (1, true, stay))` — in state `0` reading `false`, go to state
`1`, write `true`, stay.  On input `[false]` it reaches the accepting state `1` in one step.

## What is proved (clean axioms, no `sorry`)

* **`flipTable`** — the concrete one-rule transition table.
* **`flip_applyTrans`** — the rule's effect: `applyTrans (0,0,[false]) rule = (1,0,[true])` (exercises `writeAt`,
  `moveHead`).
* **`flip_step`** — the rule fires: `concreteStep flipTable (0,0,[false]) (1,0,[true])` (the left-hand side matches
  `(state, readSym)`).
* **`flip_reachIn`** — a one-step run in the abstract model: `reachIn (toNTM flipTable) 1 (0,0,[false]) (1,0,[true])`.
* **`flip_accepts`** — `acceptsWithin (toNTM flipTable) [false] 1`: the machine accepts `[false]` within one step.

## Honest scope

This is a **worked realization** of the existing transition-table model: a concrete table-driven machine is run and its
computation proved correct step by step, exercising the whole apparatus (`readSym`/`writeAt`/`moveHead`/`applyTrans`/
`concreteStep`/`reachIn`/`acceptsWithin`).  It confirms the transition-table semantics compute as intended; it does not
build the *time-bounded universal* simulation (the clocked universal machine over this model), which is the genuine
content the hierarchy `DiagonalInNexp`-style sockets need.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ConcreteTMRun

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn acceptsWithin)

/-- **A concrete one-rule transition table.**  In state `0` reading `false`: go to state `1`, write `true`, stay
(move `2`). -/
def flipTable : TMachine := [((0, false), (1, true, (2 : Fin 3)))]

/-- **The rule's effect (PROVED).**  Applying the rule to `(0,0,[false])` writes `true` and stays: `(1,0,[true])`. -/
theorem flip_applyTrans :
    applyTrans (0, 0, [false]) ((0, false), (1, true, (2 : Fin 3))) = (1, 0, [true]) := by decide

/-- **The rule fires (PROVED).**  `concreteStep flipTable (0,0,[false]) (1,0,[true])`: the left-hand side matches
`(state 0, readSym = false)`, and the right-hand side is `applyTrans`. -/
theorem flip_step : concreteStep flipTable (0, 0, [false]) (1, 0, [true]) :=
  ⟨((0, false), (1, true, (2 : Fin 3))), by decide, by decide, by decide⟩

/-- **A one-step run in the abstract model (PROVED).**  `reachIn (toNTM flipTable) 1 (0,0,[false]) (1,0,[true])`. -/
theorem flip_reachIn : reachIn (toNTM flipTable) 1 (0, 0, [false]) (1, 0, [true]) :=
  ⟨(1, 0, [true]), flip_step, rfl⟩

/-- **The machine accepts (PROVED).**  `acceptsWithin (toNTM flipTable) [false] 1`: from `init [false] = (0,0,[false])`
the machine reaches the accepting state `1` within one step. -/
theorem flip_accepts : acceptsWithin (toNTM flipTable) [false] 1 :=
  ⟨1, le_refl 1, (1, 0, [true]), flip_reachIn, rfl⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ConcreteTMRun

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteTMRun.flip_step
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteTMRun.flip_accepts

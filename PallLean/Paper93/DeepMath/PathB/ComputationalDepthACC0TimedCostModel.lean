import Mathlib

/-!
# Mathlib's step-counted cost model: time-weakening (Williams machine model, cost-model foundation) (PROVED)

**Correction to the earlier "Mathlib has no cost model" framing.**  Mathlib *does* provide a step-counted
cost model — `Turing.EvalsToInTime f a b m` (config `a` reaches `b` by iterating the step function `f` in
`≤ m` steps) and the `Turing.TM2ComputableInTime` / `TM2ComputableInPolyTime` complexity classes — and it
already has **sequential composition** with additive time (`Turing.EvalsToInTime.trans`).

What it lacks is **time-weakening** (more budget still suffices), a basic monotonicity foundation; we add
it:

  `evalsToInTime_weaken` — `EvalsToInTime f a b m → m ≤ m' → EvalsToInTime f a b m'`.

This is the cost-model analogue of `ACC0TimedModelProps.timedEnum_accept_mono` (acceptance monotone in the
budget): the *same* "more time never hurts" fact, now in Mathlib's TM-level framework.  Together with
`EvalsToInTime.trans` (additive overhead under composition) it gives the two structural rules any
overhead/timing analysis is built from.

## What is proved (clean axioms, no `sorry`)

* `evalsToInTime_weaken` — time-weakening for Mathlib's `EvalsToInTime`.

## Honest scope

Cost-model foundation (weakening; composition already in Mathlib).  The genuine remaining ingredient for
the Williams time hierarchy is the **efficient universal simulator** — a `TM2ComputableInTime` universal
machine simulating `t` steps in `t·polylog` (Hennie–Stearns) — which is **not** in Mathlib's `Turing`
library, plus a bridge from the `Code.evaln` timed enumeration (`ACC0TimedEnumeration`) to this TM model.
That is the deep Williams-strength gap, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimedCostModel

open Turing

/-- **Time-weakening for `EvalsToInTime` (proved): more budget still suffices.**  The TM-level analogue of
`timedEnum_accept_mono`. -/
def evalsToInTime_weaken {σ : Type*} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

/-!
**Cost-model weakening proved.**  Mathlib's step-counted model (`EvalsToInTime`) now has both weakening
(here) and composition (`EvalsToInTime.trans`, additive time) — the structural timing rules.  The
efficient universal simulator (`t·polylog` overhead) and the `Code.evaln`-to-`TM2` bridge remain the deep
machine-model gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TimedCostModel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedCostModel.evalsToInTime_weaken

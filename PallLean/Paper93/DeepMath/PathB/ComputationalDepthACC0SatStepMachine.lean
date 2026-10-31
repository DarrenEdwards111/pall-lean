import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatMachine

/-!
# An operational step machine for the cell search

`…ACC0SatMachine` made time a `steps` field.  This file grounds it in a concrete **operational step machine**: a
small interpreter that processes one cell per step, with an explicit `step`/`runFor` semantics.  We prove the
machine **computes the SAT answer**, in **exactly `#cells` steps**, and that this step count carries the `< 2^n`
bound.  So "time" is now the number of `step` transitions of a defined machine — operational, not abstract.

The machine: state = (accumulator `acc`, remaining cell list `todo`).  Each `step` consumes one cell, OR-ing its
`cellPredicate` into `acc`.  After `#cells` steps from `⟨false, cells⟩` it halts (`todo = []`) with
`acc = (cells satisfiable)`.

## What is proved (clean axioms, no `sorry`)

* `foldl_or_eq_any` — the OR-accumulation equals `List.any` (the machine's accumulator is the disjunction).
* `runFor_length` — running `#todo` steps drains the list and folds the accumulator.
* `machine_decides` — **the machine computes SAT**: after `#cells` steps its `acc` is `true` iff the circuit is
  satisfiable.
* `machine_steps_le`, `machine_beats_bruteforce` — **the machine time bound**: the machine halts in `≤ (n+1)^k`
  steps, and `< 2^n` in the small-gate regime.

## Honest scope

This is a genuine operational model — a step function with a transition count — realizing the cell search, so the
time bound is now a bound on actual machine transitions.  It is a *list-processing step machine* (one cell per
step), **not** a Turing machine with tape/head/input encoding, and it does not perform the `n^ε` accounting.  So it
grounds "machine time" operationally for the cell‑search cost model; the full Turing‑machine `2^{n-n^ε}` ACC⁰‑SAT
analysis remains the named gap (the genuine Williams content).  Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatStepMachine

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost
open PallLean.Paper93.DeepMath.PathB.ACC0SatMachine

variable {n k : ℕ}

/-- **OR-accumulation equals `any` (proved).** -/
theorem foldl_or_eq_any {α : Type*} (p : α → Bool) (l : List α) (a : Bool) :
    l.foldl (fun b w => b || p w) a = (a || l.any p) := by
  induction l generalizing a with
  | nil => simp
  | cons w ws ih => simp [List.foldl_cons, List.any_cons, ih, Bool.or_assoc]

/-- Machine state: accumulated answer and the remaining cells to examine. -/
structure MachineState (n k : ℕ) where
  acc : Bool
  todo : List (Fin k → ℕ)

/-- One machine step: consume the next cell, OR-ing its acceptance into the accumulator. -/
def step (C : Depth2ModCircuit n k) (s : MachineState n k) : MachineState n k :=
  match s.todo with
  | [] => s
  | w :: ws => ⟨s.acc || cellPredicate C w, ws⟩

/-- Run the machine for `t` steps. -/
def runFor (C : Depth2ModCircuit n k) : ℕ → MachineState n k → MachineState n k
  | 0, s => s
  | t + 1, s => runFor C t (step C s)

/-- **Running `#todo` steps drains the list and folds the accumulator (proved).** -/
theorem runFor_length (C : Depth2ModCircuit n k) (a : Bool) (ws : List (Fin k → ℕ)) :
    runFor C ws.length ⟨a, ws⟩ = ⟨ws.foldl (fun b w => b || cellPredicate C w) a, []⟩ := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    show runFor C (ws.length + 1) ⟨a, w :: ws⟩ = _
    rw [runFor]
    show runFor C ws.length ⟨a || cellPredicate C w, ws⟩ = _
    rw [ih]
    rw [List.foldl_cons]

/-- **The machine computes SAT (proved): after `#cells` steps its accumulator is `true` iff the circuit is
satisfiable.** -/
theorem machine_decides (C : Depth2ModCircuit n k) :
    (runFor C ((Finset.univ.image (weightVec C.supports)).toList.length)
      ⟨false, (Finset.univ.image (weightVec C.supports)).toList⟩).acc = true
    ↔ Satisfiable C.eval := by
  rw [runFor_length]
  show ((Finset.univ.image (weightVec C.supports)).toList.foldl
    (fun b w => b || cellPredicate C w) false) = true ↔ _
  rw [foldl_or_eq_any, Bool.false_or]
  exact decideSAT_correct C

/-- The machine's running time equals the number of cells (= `cellSearch` steps). -/
theorem machine_steps_eq (C : Depth2ModCircuit n k) :
    (Finset.univ.image (weightVec C.supports)).toList.length = (cellSearch C).steps := by
  rw [Finset.length_toList]; rfl

/-- **The machine time bound (proved): the machine halts in `≤ (n+1)^k` steps.** -/
theorem machine_steps_le (C : Depth2ModCircuit n k) :
    (Finset.univ.image (weightVec C.supports)).toList.length ≤ (n + 1) ^ k := by
  rw [Finset.length_toList]
  exact imageSearchCost_le C.supports

/-- **The machine beats brute force (proved): in the small-gate regime it halts in `< 2^n` steps.** -/
theorem machine_beats_bruteforce (C : Depth2ModCircuit n k) (hregime : (n + 1) ^ k < 2 ^ n) :
    (Finset.univ.image (weightVec C.supports)).toList.length < 2 ^ n :=
  lt_of_le_of_lt (machine_steps_le C) hregime

end PallLean.Paper93.DeepMath.PathB.ACC0SatStepMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatStepMachine.runFor_length
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatStepMachine.machine_decides
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatStepMachine.machine_beats_bruteforce

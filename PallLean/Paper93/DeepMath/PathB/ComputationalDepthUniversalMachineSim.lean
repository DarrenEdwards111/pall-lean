import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineRecovery

/-!
# Universal machine, bricks 3 & 4: the simulation, proved correct against `ofData`

Bricks 1/2/2b made a machine description faithfully serialisable and readable.  This file builds the
SIMULATION: a universal step `uStep` that reads the serialised transition table + halt list and
advances an encoded configuration, and its iterate `uRun`, both proved to match `ofData(data)`'s own
`step`/`run` exactly.  This is the semantic core of the universal machine — the decoded description
genuinely drives the same computation.

## What is proved

* **`serialHalt` / `st_val_mem_serialHalt`** — the halt-state list, with `c.st.val ∈ serialHalt data
  ↔ ofData(data).halt c.st`.  (Halt info alongside the rules; on the tape it is a brick-1 codec
  extension, flagged.)
* **`moveHeadN` / `moveHead_eq`** — the `ℕ`-valued head move, agreeing with `ComposableMachine`'s
  `moveHead` on `m.val`.
* **`uStep`** — one universal step: at a halting state, stay; else look up `(state, symbol)` in the
  rules and apply `(next state, write, move)`.
* **`uStep_correct`** (proved) — `uStep (serialRules data) (serialHalt data) (encodeConfig c) =
  encodeConfig (step (ofData data) c)`: the universal step mirrors the real machine's step, via
  `lookupRule_recovers`, `moveHead_eq`, and the halt correspondence.
* **`uRun_correct`** (proved) — the iterate agrees at every clock: `uRun … t (encodeConfig c) =
  encodeConfig (run (ofData data) t c)`.  The universal machine, run for any number of steps,
  computes exactly what the simulated machine does.

## Honest scope

Bricks 1–4 give a faithful, decodable machine description AND a step/run simulation proved correct
against `ofData` — the complete SEMANTIC universal simulation.  What remains for
`DiagonalAgainstCanon` (unchanged): (i) implementing `uStep`/`uRun` AS a `ComposableMachine` that
does this with actual tape operations within a polynomial clock (the tape-layout engineering, plus
the binary-encoding refinement flagged in brick 1, for the clock bound); (ii) the lazy-delay
diagonal (brick 5), the nondeterministic construction that dodges the co-`NTIME` trap
(`naiveDiag_is_complement`) — genuine research-scale labor, not built or faked here.  This file
claims exactly a verified semantic simulation.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineSim

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial
open PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge
open PallLean.Paper93.DeepMath.PathB.UniversalMachineRecovery

variable {k : ℕ}

/-- The list of halting states. -/
def serialHalt (data : FinMachineData k) : List ℕ :=
  (List.finRange k).filterMap (fun i => if data.2.1 i = true then some i.val else none)

/-- **The halt list is faithful (proved).**  `c.st.val ∈ serialHalt data ↔ ofData(data) halts at
`c.st`. -/
theorem st_val_mem_serialHalt (data : FinMachineData k) (s : Fin k) :
    s.val ∈ serialHalt data ↔ data.2.1 s = true := by
  rw [serialHalt, List.mem_filterMap]
  constructor
  · rintro ⟨i, _, hi⟩
    by_cases h : data.2.1 i = true
    · simp only [if_pos h, Option.some.injEq] at hi
      have : i = s := Fin.val_injective hi
      rw [← this]; exact h
    · simp [h] at hi
  · intro h
    exact ⟨s, List.mem_finRange s, by simp [h]⟩

/-- `ℕ`-valued head move, matching `ComposableMachine.moveHead`. -/
def moveHeadN (h : ℕ) (mv : ℕ) : ℕ :=
  if mv = 0 then h - 1 else if mv = 1 then h + 1 else if mv = 2 then h else 0

/-- **`moveHeadN` matches `moveHead` (proved).** -/
theorem moveHead_eq (h : ℕ) (m : Move) : moveHead h m = moveHeadN h m.val := by
  fin_cases m <;> rfl

/-- Apply an optional write. -/
def applyWrite (tp : List Bool) (hd : ℕ) : Option Bool → List Bool
  | none => tp
  | some b => writeAt tp hd b

/-- A configuration encoded for the universal machine: `(state, head, tape)`. -/
abbrev UConfig : Type := ℕ × ℕ × List Bool

/-- Encode a real configuration. -/
def encodeConfig {data : FinMachineData k} (c : Cfg (ofData data)) : UConfig :=
  (c.st.val, c.hd, c.tp)

/-- **One universal step.** -/
def uStep (rules : List Rule) (halts : List ℕ) : UConfig → UConfig
  | (s, hd, tp) =>
      if s ∈ halts then (s, hd, tp)
      else
        match lookupRule rules s (tp.getD hd false) with
        | some (ns, w, mv) => (ns, moveHeadN hd mv, applyWrite tp hd w)
        | none => (s, hd, tp)

/-- **The universal step mirrors the real step (proved).** -/
theorem uStep_correct (data : FinMachineData k) (c : Cfg (ofData data)) :
    uStep (serialRules data) (serialHalt data) (encodeConfig c)
      = encodeConfig (step (ofData data) c) := by
  show uStep (serialRules data) (serialHalt data) (c.st.val, c.hd, c.tp) = _
  by_cases hhalt : data.2.1 c.st = true
  · rw [uStep, if_pos ((st_val_mem_serialHalt data c.st).mpr hhalt)]
    rw [step_of_halted (ofData data) (show (ofData data).halt c.st = true from hhalt)]
    rfl
  · have hnh : c.st.val ∉ serialHalt data :=
      fun hm => hhalt ((st_val_mem_serialHalt data c.st).mp hm)
    rw [uStep, if_neg hnh, lookupRule_recovers]
    have hstep : step (ofData data) c =
        ⟨(data.2.2.1 c.st (c.tp.getD c.hd false)).1,
          moveHead c.hd (data.2.2.1 c.st (c.tp.getD c.hd false)).2.2,
          applyWrite c.tp c.hd (data.2.2.1 c.st (c.tp.getD c.hd false)).2.1⟩ := by
      unfold step
      rw [show (ofData data).halt c.st = false from by
        simpa using hhalt]
      rfl
    rw [hstep]
    show (_, moveHeadN c.hd _, _) = (_, moveHead c.hd _, _)
    rw [moveHead_eq]

/-- Iterate the universal step. -/
def uRun (rules : List Rule) (halts : List ℕ) (t : ℕ) (cfg : UConfig) : UConfig :=
  (uStep rules halts)^[t] cfg

/-- **The universal run mirrors the real run at every clock (proved).** -/
theorem uRun_correct (data : FinMachineData k) (t : ℕ) (c : Cfg (ofData data)) :
    uRun (serialRules data) (serialHalt data) t (encodeConfig c)
      = encodeConfig (run (ofData data) t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    show (uStep (serialRules data) (serialHalt data))^[t + 1] (encodeConfig c) = _
    rw [Function.iterate_succ_apply']
    show uStep (serialRules data) (serialHalt data)
      (uRun (serialRules data) (serialHalt data) t (encodeConfig c)) = _
    rw [ih, uStep_correct, run_succ]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineSim

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSim.uStep_correct
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSim.uRun_correct

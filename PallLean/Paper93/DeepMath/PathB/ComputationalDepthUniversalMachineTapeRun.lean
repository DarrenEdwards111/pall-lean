import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineTapeStep

/-!
# Universal machine: the tape-level RUN simulates the machine — the functional core, complete

`uStepOnTape` advances an encoded configuration by one step on the tape.  Iterating it gives
`uRunOnTape`, and this file proves the culmination: running the universal step-on-tape `t` times
computes exactly the encoding of `ofData(data)`'s own run after `t` steps.  The functional universal
machine is now complete — a single tape carrying description + halt-list + configuration, and a
tape-level run proved to simulate the real machine at every clock.

## What is proved

* **`uRunOnTape`** — iterate `uStepOnTape` `t` times.
* **`uRunOnTape_correct`** (proved) — `uRunOnTape t (encodeTape data c) = encodeTape data (uRun …
  t c)`: the tape-level run advances the encoded configuration by exactly `t` semantic `uStep`s
  (induction + `uStepOnTape_correct`).
* **`uRunOnTape_simulates`** (proved) — the capstone: `uRunOnTape t (encodeTape data (encodeConfig
  c₀)) = encodeTape data (encodeConfig (run (ofData data) t c₀))`.  The universal machine, reading a
  machine and a start configuration off its tape and running `t` tape-steps, produces the encoding of
  `ofData(data)`'s configuration after `t` real steps.  This is the full semantic universal
  simulation, at the tape level.

## Honest scope

Bricks 1–4, 3.5, tape-step, and this run together are the complete FUNCTIONAL universal machine: the
whole state lives on one Bool tape, every transition is recovered exactly, and the tape-level run
provably tracks the real machine step-for-step.  What remains (unchanged): realise `uStepOnTape` with
bounded head-move operations of a fixed-control `ComposableMachine` (the tape-layout loop), the binary
refinement (for the polynomial clock), and the lazy-delay diagonal (brick 5).  This file claims
exactly a verified tape-level simulation of the run.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeRun

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSim
open PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig
open PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeStep

variable {k : ℕ}

/-- Iterate the tape-level universal step `t` times. -/
def uRunOnTape (t : ℕ) (tape : List Bool) : List Bool :=
  (uStepOnTape)^[t] tape

/-- **The tape-level run is correct (proved).**  Running `t` tape-steps advances the encoded
configuration by exactly `t` semantic `uStep`s. -/
theorem uRunOnTape_correct (data : FinMachineData k) (t : ℕ) (c : Conf) :
    uRunOnTape t (encodeTape data c)
      = encodeTape data (uRun (serialRules data) (serialHalt data) t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    show (uStepOnTape)^[t + 1] (encodeTape data c) = _
    rw [Function.iterate_succ_apply']
    show uStepOnTape (uRunOnTape t (encodeTape data c)) = _
    rw [ih, uStepOnTape_correct]
    congr 1
    exact (Function.iterate_succ_apply' (uStep (serialRules data) (serialHalt data)) t c).symm

/-- **The capstone (proved).**  The universal machine, reading a machine and a start configuration
off its tape and running `t` tape-steps, produces the encoding of `ofData(data)`'s configuration
after `t` real steps.  The complete semantic universal simulation, at the tape level. -/
theorem uRunOnTape_simulates (data : FinMachineData k) (t : ℕ) (c₀ : Cfg (ofData data)) :
    uRunOnTape t (encodeTape data (encodeConfig c₀))
      = encodeTape data (encodeConfig (run (ofData data) t c₀)) := by
  rw [uRunOnTape_correct, uRun_correct]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeRun

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeRun.uRunOnTape_correct
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeRun.uRunOnTape_simulates

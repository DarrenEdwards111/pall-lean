import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineSim
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineConfig

/-!
# Universal machine, brick 5-prep: one universal step on the tape representation

Bricks 1 / 3.5 put the machine description and the configuration on the Bool tape; bricks 3 / 4
proved the semantic step/run correct.  This file joins them: a **tape-level universal step**
`uStepOnTape` that reads the machine, its halt list, and the configuration off ONE tape, applies
`uStep`, and writes the new configuration back — proved correct against the semantic `uStep`.  This
is the functional core of the `ComposableMachine` universal control loop (the remaining tape-layout
engineering realises it with head moves).

## The tape layout

`encodeMachine (serialOf data) ++ encList encNat (serialHalt data) ++ encodeConf c` — description,
halt-state list, configuration.  All three are decodable (bricks 1, 3.5) and the halt list is added
here as a length-prefixed `ℕ`-list (the `SerialMachine` `halt`-field extension flagged in brick 2).

## What is proved

* **`uStepOnTape`** — decode the machine, halt list, and configuration from the tape; apply `uStep`
  with the decoded rules and halts; re-encode with the new configuration (machine and halts
  unchanged).  Malformed tapes are left fixed.
* **`uStepOnTape_correct`** (proved) — on a well-formed tape,
  `uStepOnTape (tape data c) = tape data (uStep (serialRules data) (serialHalt data) c)`: one
  tape-level step advances the encoded configuration by exactly one semantic `uStep`, which (bricks
  3/4) is exactly `ofData(data)`'s own step.

## Honest scope

`uStepOnTape` is the universal control as a FUNCTION on the tape — the last piece before the actual
`ComposableMachine`.  What remains (unchanged): realise `uStepOnTape` with bounded head-move
operations of a fixed-control `ComposableMachine` (the tape-layout loop), the binary refinement (for
the polynomial clock), and the lazy-delay diagonal (brick 5) that dodges the co-`NTIME` trap.  This
file claims exactly a verified functional tape-step.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeStep

open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial
open PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSim
open PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig

variable {k : ℕ}

/-- The full tape: machine description, halt-state list, configuration. -/
def encodeTape (data : FinMachineData k) (c : Conf) : List Bool :=
  encodeMachine (serialOf data) ++ encList encNat (serialHalt data) ++ encodeConf c

/-- **One universal step on the tape.**  Decode the machine, halt list, and configuration; apply
`uStep` with the decoded rules and halts; re-encode with the new configuration (machine and halts
unchanged). -/
def uStepOnTape (tape : List Bool) : List Bool :=
  match decodeMachine tape with
  | none => tape
  | some (sm, l1) =>
    match decList decNat l1 with
    | none => tape
    | some (halts, l2) =>
      match decodeConf l2 with
      | none => tape
      | some (c, _) =>
        encodeMachine sm ++ encList encNat halts ++ encodeConf (uStep sm.rules halts c)

/-- **The tape-level step is correct (proved).**  On a well-formed tape, one `uStepOnTape` advances
the encoded configuration by exactly one semantic `uStep` — which (bricks 3/4) is `ofData(data)`'s
own step. -/
theorem uStepOnTape_correct (data : FinMachineData k) (c : Conf) :
    uStepOnTape (encodeTape data c)
      = encodeTape data (uStep (serialRules data) (serialHalt data) c) := by
  unfold uStepOnTape encodeTape
  simp only [List.append_assoc, decodeMachine_encodeMachine,
    decList_encList encNat decNat decNat_encNat, decodeConf_encodeConf_nil]
  rfl

end PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeStep

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeStep.uStepOnTape_correct

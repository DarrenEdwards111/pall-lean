import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineTapeStep

/-!
# Universal machine: reading the decision off the tape (halt + accept)

`uStepOnTape` advances the simulated configuration; a universal machine acting as an NTIME verifier
must also READ, from the same tape, whether the simulated machine has halted and whether it accepts.
This file builds those two reads — `tapeHalted` and `tapeAccepts` — and proves they match
`ofData(data)`'s own `halt`/`accept` on the simulated state.  Together with `uStepOnTape` /
`uRunOnTape` this completes the tape INTERFACE: run the machine, then read the verdict, all off one
Bool tape.

## What is proved

* **`st_val_mem_serialAccept`** — `s.val ∈ (serialOf data).accept ↔ ofData(data) accepts at `s``
  (mirror of the halt fact).
* **`tapeHalted` / `tapeHalted_correct`** — decode the halt list and configuration, test the state:
  `tapeHalted (encodeTape data (encodeConfig c)) = ofData(data).halt c.st`.
* **`tapeAccepts` / `tapeAccepts_correct`** — decode the machine's accept list and configuration,
  test the state: `tapeAccepts (encodeTape data (encodeConfig c)) = ofData(data).accept c.st`.

## Honest scope

The tape interface is now complete: `uStepOnTape` (advance), `tapeHalted` (halted?), `tapeAccepts`
(accepting?) — everything an NTIME verifier reads and writes, all verified off one tape.  What
remains for `DiagonalAgainstCanon` (unchanged): realise these tape functions as bounded head-move
operations of a fixed-control `ComposableMachine` (the tape-layout loop), and the lazy-delay diagonal
(brick 5).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineDecision

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial
open PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSim
open PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig
open PallLean.Paper93.DeepMath.PathB.UniversalMachineTapeStep

variable {k : ℕ}

/-- `decide (b = true) = b` for a Bool `b` — used to collapse the decoded membership test back to the
machine's own Bool-valued halt/accept flag.  Stated as a helper so it can be applied by unification
(casing on the stuck projection `data.2.1 c.st` in place fails to build a type-correct motive). -/
private theorem decide_bool_eq (b : Bool) : decide (b = true) = b := by cases b <;> rfl

/-- **The accept list is faithful (proved).**  `s.val ∈ serialAccept data ↔ ofData(data)` accepts at
`s` (mirror of `st_val_mem_serialHalt`). -/
theorem st_val_mem_serialAccept (data : FinMachineData k) (s : Fin k) :
    s.val ∈ serialAccept data ↔ data.2.2.2 s = true := by
  rw [serialAccept, List.mem_filterMap]
  constructor
  · rintro ⟨i, _, hi⟩
    by_cases h : data.2.2.2 i = true
    · simp only [if_pos h, Option.some.injEq] at hi
      rw [← Fin.val_injective hi]; exact h
    · simp [h] at hi
  · intro h
    exact ⟨s, List.mem_finRange s, by simp [h]⟩

/-- **Read: has the simulated machine halted?**  Decode the halt list and configuration; test the
state. -/
def tapeHalted (tape : List Bool) : Bool :=
  match decodeMachine tape with
  | none => false
  | some (_, l1) =>
    match decList decNat l1 with
    | none => false
    | some (halts, l2) =>
      match decodeConf l2 with
      | none => false
      | some (c, _) => decide (c.1 ∈ halts)

/-- **Read: does the simulated machine accept?**  Decode the machine's accept list and configuration;
test the state. -/
def tapeAccepts (tape : List Bool) : Bool :=
  match decodeMachine tape with
  | none => false
  | some (sm, l1) =>
    match decList decNat l1 with
    | none => false
    | some (_, l2) =>
      match decodeConf l2 with
      | none => false
      | some (c, _) => decide (c.1 ∈ sm.accept)

/-- **The halt read is correct (proved).**  `tapeHalted (encodeTape data (encodeConfig c)) =
ofData(data).halt c.st`. -/
theorem tapeHalted_correct (data : FinMachineData k) (c : Cfg (ofData data)) :
    tapeHalted (encodeTape data (encodeConfig c)) = data.2.1 c.st := by
  unfold tapeHalted encodeTape
  simp only [List.append_assoc, decodeMachine_encodeMachine,
    decList_encList encNat decNat decNat_encNat, decodeConf_encodeConf_nil]
  show decide (c.st.val ∈ serialHalt data) = _
  rw [decide_eq_decide.mpr (st_val_mem_serialHalt data c.st)]
  exact decide_bool_eq _

/-- **The accept read is correct (proved).**  `tapeAccepts (encodeTape data (encodeConfig c)) =
ofData(data).accept c.st`. -/
theorem tapeAccepts_correct (data : FinMachineData k) (c : Cfg (ofData data)) :
    tapeAccepts (encodeTape data (encodeConfig c)) = data.2.2.2 c.st := by
  unfold tapeAccepts encodeTape
  simp only [List.append_assoc, decodeMachine_encodeMachine,
    decList_encList encNat decNat decNat_encNat, decodeConf_encodeConf_nil]
  show decide (c.st.val ∈ (serialOf data).accept) = _
  show decide (c.st.val ∈ serialAccept data) = _
  rw [decide_eq_decide.mpr (st_val_mem_serialAccept data c.st)]
  exact decide_bool_eq _

end PallLean.Paper93.DeepMath.PathB.UniversalMachineDecision

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineDecision.tapeHalted_correct
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineDecision.tapeAccepts_correct

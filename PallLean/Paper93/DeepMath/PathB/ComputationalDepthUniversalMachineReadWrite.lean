import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineHeadMove

/-!
# Head-move construction, brick 3: local read / write primitives

Bricks 1–2 walk the head across the tape without ever writing.  The universal control also has to act
LOCALLY at the cell under the head: read the simulated symbol into its finite control (to look up the
rule), and write the new symbol back.  This brick builds those two primitives as real fixed-control
`ComposableMachine`s and proves them, including the semantically load-bearing read-after-write
consistency fact.

## What is proved

* **`writeAt_getD_self`** — read-after-write: `(writeAt tape p w).getD p false = w`.  Writing `w` at
  `p` and reading `p` back returns `w`.  This is why the local write is usable by later stages.
* **`readBit`** — a two-live-state `ComposableMachine` (`State = Option Bool`; `none` = reading,
  `some b` = "read `b`").  One step reads the cell under the head into the control and halts; head and
  tape untouched.
    * `readBit_run` — `run readBit 1 c = ⟨some (c.tp.getD c.hd false), c.hd, c.tp⟩`.
    * `readBit_accept` — the decision read equals the cell: `readBit.accept (run readBit 1 c).st =
      c.tp.getD c.hd false`.
* **`writeBit w`** — a two-state `ComposableMachine` that writes the fixed bit `w` at the head and
  halts; head unchanged, tape `= writeAt`.
    * `writeBit_run` — `run (writeBit w) 1 c = ⟨true, c.hd, writeAt c.tp c.hd w⟩`.
    * `writeBit_reads_back` — after the write, reading the head returns `w` (the machine-level
      read-after-write, from `writeAt_getD_self`).

## Honest scope

These are the local read/write primitives — the write-analog of the field-walk — realised as real
`ComposableMachine`s and proved, with read-after-write consistency.  With bricks 1–2 (navigation) they
are the pieces the data-dependent seek and the rule-application will compose.  What remains for the
full `uStepOnTape` control: the data-dependent seek (unary counter with tape mutation/restoration),
rule lookup, and sequencing; then the lazy-delay diagonal (brick 5).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial

/-! ## Read-after-write consistency -/

/-- **Read-after-write (proved).**  Writing `w` at position `p` and reading position `p` back returns
`w`. -/
theorem writeAt_getD_self (tape : List Bool) (p : ℕ) (w : Bool) :
    (writeAt tape p w).getD p false = w := by
  have hlt : p < (tape ++ List.replicate (p + 1 - tape.length) false).length := by
    rw [List.length_append, List.length_replicate]; omega
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt]
  rfl

/-! ## The local read primitive -/

/-- **The read primitive.**  A fixed-control `ComposableMachine`; `State = Option Bool` with `none` =
"still reading" and `some b` = "read `b`" (halted).  One step reads the cell under the head into the
control; the head does not move and the tape is untouched. -/
def readBit : Machine where
  State := Option Bool
  fin := inferInstance
  dec := inferInstance
  start := none
  halt := fun s => s.isSome
  δ := fun _ b => (some b, none, (2 : Move))
  accept := fun s => s.getD false

theorem readBit_step {c : Cfg readBit} (hs : c.st = none) :
    step readBit c = ⟨some (c.tp.getD c.hd false), c.hd, c.tp⟩ := by
  have hne : readBit.halt c.st = false := by rw [hs]; rfl
  have hstep : step readBit c
      = ⟨(readBit.δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd (readBit.δ c.st (c.tp.getD c.hd false)).2.2,
         (match (readBit.δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
    unfold step; rw [hne]; rfl
  rw [hstep]; rfl

/-- **The read is correct (proved).**  One step reads the cell under the head into the control state;
head and tape unchanged. -/
theorem readBit_run (c : Cfg readBit) (hs : c.st = none) :
    run readBit 1 c = ⟨some (c.tp.getD c.hd false), c.hd, c.tp⟩ := by
  rw [show run readBit 1 c = step readBit c from rfl, readBit_step hs]

/-- **The decision read equals the cell (proved).**  `readBit.accept (run readBit 1 c).st =
c.tp.getD c.hd false`. -/
theorem readBit_accept (c : Cfg readBit) (hs : c.st = none) :
    readBit.accept (run readBit 1 c).st = c.tp.getD c.hd false := by
  rw [readBit_run c hs]; rfl

/-! ## The local write primitive -/

/-- **The write primitive** (fixed bit `w`).  A fixed-control `ComposableMachine`; `State = Bool`
with `false` = "writing", `true` = "done" (halted).  One step writes `w` at the cell under the head
and halts; the head does not move. -/
def writeBit (w : Bool) : Machine where
  State := Bool
  fin := inferInstance
  dec := inferInstance
  start := false
  halt := fun s => s
  δ := fun _ _ => (true, some w, (2 : Move))
  accept := fun _ => false

theorem writeBit_step (w : Bool) {c : Cfg (writeBit w)} (hs : c.st = false) :
    step (writeBit w) c = ⟨true, c.hd, writeAt c.tp c.hd w⟩ := by
  have hstep : step (writeBit w) c
      = ⟨((writeBit w).δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd ((writeBit w).δ c.st (c.tp.getD c.hd false)).2.2,
         (match ((writeBit w).δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w' => writeAt c.tp c.hd w')⟩ := by
    unfold step; rw [show (writeBit w).halt c.st = false from hs]; rfl
  rw [hstep]; rfl

/-- **The write is correct (proved).**  One step writes `w` at the head; head unchanged, tape
`= writeAt c.tp c.hd w`. -/
theorem writeBit_run (w : Bool) (c : Cfg (writeBit w)) (hs : c.st = false) :
    run (writeBit w) 1 c = ⟨true, c.hd, writeAt c.tp c.hd w⟩ := by
  rw [show run (writeBit w) 1 c = step (writeBit w) c from rfl, writeBit_step w hs]

/-- **The write reads back (proved).**  After `writeBit w` runs, the cell under the head holds `w` —
the machine-level read-after-write, from `writeAt_getD_self`. -/
theorem writeBit_reads_back (w : Bool) (c : Cfg (writeBit w)) (hs : c.st = false) :
    (run (writeBit w) 1 c).tp.getD (run (writeBit w) 1 c).hd false = w := by
  rw [writeBit_run w c hs]; exact writeAt_getD_self c.tp c.hd w

end PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite.readBit_accept
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite.writeBit_reads_back

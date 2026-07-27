import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineReadWrite

/-!
# Head-move construction, brick 5: moving the simulated head as a marker shift

Brick 4 chose the clean representation of the simulated head — a position MARKER (a single `true`) — so
that "seek to the head" is a write-free scan.  This brick delivers the other half of that choice: with
the head marked, a simulated LEFT/RIGHT move is just *shifting the marker one cell* — clear it here, set
it next door — two of the brick-3 local writes.  No counter, no shuffling: the marked representation
makes head motion a bounded local edit.

To state "the rest of the tape is untouched" we first prove the write-at-a-different-position lemmas
(reusable for every later write-based stage).

## What is proved

* **`getD_append_replicate_false`** — padding a tape with trailing `false`s does not change any
  `getD … false`.
* **`writeAt_getD_of_ne`** — writing at `p` leaves every other cell `q ≠ p` unchanged:
  `(writeAt tape p w).getD q false = tape.getD q false`.
* **`shiftRight`** — a three-state `ComposableMachine` (`clr → setm → done`): positioned ON the marker,
  it clears the current cell (write `false`, move right) then sets the next cell (write `true`), halting.
* **`shiftRight_run`** — `run shiftRight 2 c = ⟨done, c.hd + 1, writeAt (writeAt c.tp c.hd false)
  (c.hd + 1) true⟩`.
* **`shiftRight_sets_new`** — the marker is now at `c.hd + 1` (`getD (c.hd+1) = true`).
* **`shiftRight_clears_old`** — the old marker is gone (`getD c.hd = false`).
* **`shiftRight_preserves`** — every other cell (`q ≠ c.hd, c.hd+1`) is unchanged.

Together: `shiftRight` moves the head marker from `c.hd` to `c.hd + 1` and changes nothing else — a
faithful simulated head-move to the right.

## Honest scope

This completes the marked-head kit: seek to the head (brick 4, write-free), and move the head (this
brick, two local writes).  With the field-walk (1), skip (2), and read/write (3), the primitives a
simulated step decomposes into are all real, verified machines.  What remains to assemble `uStepOnTape`:
the monolithic control whose finite state carries (phase × simulated-state × read-bit) and orchestrates
seek → read → rule → write → shift, plus rule lookup; then the lazy-delay diagonal.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite

/-! ## Write-at-a-different-position lemmas -/

/-- **Trailing `false` padding is invisible to `getD … false` (proved).** -/
theorem getD_append_replicate_false (tape : List Bool) (k q : ℕ) :
    (tape ++ List.replicate k false).getD q false = tape.getD q false := by
  by_cases hq : q < tape.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hq, ← List.getD_eq_getElem?_getD]
  · have hnone : tape[q]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), List.getElem?_replicate,
      List.getD_eq_getElem?_getD, hnone]
    split <;> rfl

/-- **A write leaves every other cell unchanged (proved).**  For `p ≠ q`,
`(writeAt tape p w).getD q false = tape.getD q false`. -/
theorem writeAt_getD_of_ne (tape : List Bool) (p q : ℕ) (w : Bool) (h : p ≠ q) :
    (writeAt tape p w).getD q false = tape.getD q false := by
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, ← List.getD_eq_getElem?_getD]
  exact getD_append_replicate_false tape (p + 1 - tape.length) q

/-! ## The marker-shift machine -/

/-- Control states of `shiftRight`: clear the current marker, set the next, done. -/
inductive Shift where
  | clr : Shift
  | setm : Shift
  | done : Shift
  deriving DecidableEq

instance : Fintype Shift := ⟨{.clr, .setm, .done}, fun x => by cases x <;> decide⟩

/-- **The marker-shift machine (right).**  Positioned ON the marker: state `clr` writes `false` and
moves one cell right; state `setm` writes `true` (the new marker) in place and halts. -/
def shiftRight : Machine where
  State := Shift
  fin := inferInstance
  dec := inferInstance
  start := Shift.clr
  halt := fun s => match s with | .done => true | _ => false
  δ := fun s _ => match s with
    | .clr => (Shift.setm, some false, (1 : Move))
    | .setm => (Shift.done, some true, (2 : Move))
    | .done => (Shift.done, none, (2 : Move))
  accept := fun _ => false

theorem shiftRight_step_active {c : Cfg shiftRight} (hne : shiftRight.halt c.st = false) :
    step shiftRight c = ⟨(shiftRight.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (shiftRight.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (shiftRight.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem shiftRight_step_clr {c : Cfg shiftRight} (hs : c.st = Shift.clr) :
    step shiftRight c = ⟨Shift.setm, c.hd + 1, writeAt c.tp c.hd false⟩ := by
  rw [shiftRight_step_active (by rw [hs]; rfl), hs]; rfl

theorem shiftRight_step_setm {c : Cfg shiftRight} (hs : c.st = Shift.setm) :
    step shiftRight c = ⟨Shift.done, c.hd, writeAt c.tp c.hd true⟩ := by
  rw [shiftRight_step_active (by rw [hs]; rfl), hs]; rfl

/-- **The shift runs (proved).**  Two steps: clear the current cell, then set the next. -/
theorem shiftRight_run (c : Cfg shiftRight) (hs : c.st = Shift.clr) :
    run shiftRight 2 c
      = ⟨Shift.done, c.hd + 1, writeAt (writeAt c.tp c.hd false) (c.hd + 1) true⟩ := by
  show step shiftRight (step shiftRight c) = _
  rw [shiftRight_step_clr hs, shiftRight_step_setm rfl]

/-- **The new marker is set (proved).**  After the shift, `c.hd + 1` holds the marker. -/
theorem shiftRight_sets_new (c : Cfg shiftRight) (hs : c.st = Shift.clr) :
    (run shiftRight 2 c).tp.getD (c.hd + 1) false = true := by
  rw [shiftRight_run c hs]
  exact writeAt_getD_self (writeAt c.tp c.hd false) (c.hd + 1) true

/-- **The old marker is cleared (proved).**  After the shift, `c.hd` no longer holds the marker. -/
theorem shiftRight_clears_old (c : Cfg shiftRight) (hs : c.st = Shift.clr) :
    (run shiftRight 2 c).tp.getD c.hd false = false := by
  rw [shiftRight_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd + 1) c.hd true (by omega)]
  exact writeAt_getD_self c.tp c.hd false

/-- **The rest of the tape is untouched (proved).**  Every cell other than `c.hd` and `c.hd + 1` is
unchanged by the shift. -/
theorem shiftRight_preserves (c : Cfg shiftRight) (hs : c.st = Shift.clr)
    (q : ℕ) (hq1 : q ≠ c.hd) (hq2 : q ≠ c.hd + 1) :
    (run shiftRight 2 c).tp.getD q false = c.tp.getD q false := by
  rw [shiftRight_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd + 1) q true (by omega),
    writeAt_getD_of_ne c.tp c.hd q false (by omega)]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift.shiftRight_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift.shiftRight_sets_new
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift.shiftRight_preserves

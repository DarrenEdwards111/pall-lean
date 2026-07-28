import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineMarkerShift

/-!
# Head-move construction, brick 8: the simulated head-move LEFT (marker shift left)

Brick 5 (`shiftRight`) moves the marked simulated head one cell right; a real machine's head also moves
left.  This brick is the mirror: `shiftLeft` clears the marker at `c.hd`, moves the head one cell LEFT
(`moveHead c.hd 0 = c.hd - 1`), and sets the marker at `c.hd - 1`.  It reuses the `Shift` control states
and the write lemmas (`writeAt_getD_self`, `writeAt_getD_of_ne`) from brick 5.

The one wrinkle over `shiftRight` is truncated subtraction: at `c.hd = 0` the head can't go left
(`0 - 1 = 0`), so the "marker moved off `c.hd`" fact carries a `1 ≤ c.hd` hypothesis — matching a real
TM, whose head at cell 0 does not move left.

## What is proved

* **`shiftLeft`** — a `Shift`-state machine (`clr → setm → done`): clear (`false`, move left), then set
  (`true`, in place), halt.
* **`shiftLeft_run`** — `run shiftLeft 2 c = ⟨done, c.hd - 1, writeAt (writeAt c.tp c.hd false)
  (c.hd - 1) true⟩`.
* **`shiftLeft_sets_new`** — the marker is now at `c.hd - 1`.
* **`shiftLeft_clears_old`** (needs `1 ≤ c.hd`) — the old marker at `c.hd` is gone.
* **`shiftLeft_preserves`** — every other cell is unchanged.

With brick 5 this gives bidirectional simulated head motion: the marked head moves left or right by a
bounded local edit, and everything else on the tape is untouched.

## Honest scope

Completes the "move the simulated head" primitive (both directions).  What remains for `uStepOnTape`:
the read + rule-lookup phase between seek and shift, and the reset-to-0 per-step wrapper; then the
lazy-delay diagonal.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShiftLeft

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite (writeAt_getD_self)
open PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift (Shift writeAt_getD_of_ne)

/-- **The marker-shift machine (left).**  Positioned ON the marker: state `clr` writes `false` and
moves one cell LEFT; state `setm` writes `true` (the new marker) in place and halts. -/
def shiftLeft : Machine where
  State := Shift
  fin := inferInstance
  dec := inferInstance
  start := Shift.clr
  halt := fun s => match s with | .done => true | _ => false
  δ := fun s _ => match s with
    | .clr => (Shift.setm, some false, (0 : Move))
    | .setm => (Shift.done, some true, (2 : Move))
    | .done => (Shift.done, none, (2 : Move))
  accept := fun _ => false

theorem shiftLeft_step_active {c : Cfg shiftLeft} (hne : shiftLeft.halt c.st = false) :
    step shiftLeft c = ⟨(shiftLeft.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (shiftLeft.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (shiftLeft.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem shiftLeft_step_clr {c : Cfg shiftLeft} (hs : c.st = Shift.clr) :
    step shiftLeft c = ⟨Shift.setm, c.hd - 1, writeAt c.tp c.hd false⟩ := by
  rw [shiftLeft_step_active (by rw [hs]; rfl), hs]; rfl

theorem shiftLeft_step_setm {c : Cfg shiftLeft} (hs : c.st = Shift.setm) :
    step shiftLeft c = ⟨Shift.done, c.hd, writeAt c.tp c.hd true⟩ := by
  rw [shiftLeft_step_active (by rw [hs]; rfl), hs]; rfl

/-- **The shift runs (proved).**  Two steps: clear `c.hd` moving left, then set `c.hd - 1`. -/
theorem shiftLeft_run (c : Cfg shiftLeft) (hs : c.st = Shift.clr) :
    run shiftLeft 2 c
      = ⟨Shift.done, c.hd - 1, writeAt (writeAt c.tp c.hd false) (c.hd - 1) true⟩ := by
  show step shiftLeft (step shiftLeft c) = _
  rw [shiftLeft_step_clr hs, shiftLeft_step_setm rfl]

/-- **The new marker is set (proved).**  After the shift, `c.hd - 1` holds the marker. -/
theorem shiftLeft_sets_new (c : Cfg shiftLeft) (hs : c.st = Shift.clr) :
    (run shiftLeft 2 c).tp.getD (c.hd - 1) false = true := by
  rw [shiftLeft_run c hs]
  exact writeAt_getD_self (writeAt c.tp c.hd false) (c.hd - 1) true

/-- **The old marker is cleared (proved).**  After the shift, `c.hd` no longer holds the marker
(needs `1 ≤ c.hd`, since at cell `0` the head cannot move left). -/
theorem shiftLeft_clears_old (c : Cfg shiftLeft) (hs : c.st = Shift.clr) (hpos : 1 ≤ c.hd) :
    (run shiftLeft 2 c).tp.getD c.hd false = false := by
  rw [shiftLeft_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd - 1) c.hd true (by omega)]
  exact writeAt_getD_self c.tp c.hd false

/-- **The rest of the tape is untouched (proved).**  Every cell other than `c.hd` and `c.hd - 1` is
unchanged by the shift. -/
theorem shiftLeft_preserves (c : Cfg shiftLeft) (hs : c.st = Shift.clr)
    (q : ℕ) (hq1 : q ≠ c.hd) (hq2 : q ≠ c.hd - 1) :
    (run shiftLeft 2 c).tp.getD q false = c.tp.getD q false := by
  rw [shiftLeft_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd - 1) q true (by omega),
    writeAt_getD_of_ne c.tp c.hd q false (by omega)]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShiftLeft

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShiftLeft.shiftLeft_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShiftLeft.shiftLeft_clears_old
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShiftLeft.shiftLeft_preserves

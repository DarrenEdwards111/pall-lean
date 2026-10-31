import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineMoveRight2

/-!
# Head-move construction, brick 12: two-track simulated head-move left (`shiftLeft2`)

The mirror of brick 11.  In the two-track layout, moving the simulated head one cell *left* moves the
head-marker by two physical cells the other way: from `p = 2·hd+1` to `p - 2 = 2·(hd-1)+1`.  `shiftLeft2`
clears the marker at `p`, steps left over the intervening data cell, and sets the marker at `p - 2`.  It
reuses the `Shift2` control states (brick 11) and the write lemmas (brick 5).

As with `shiftLeft` (brick 8), truncated subtraction means the "marker moved off `p`" fact carries a
`1 ≤ c.hd` hypothesis — a real TM's head at the left end does not move further left.

## What is proved

* **`shiftLeft2`** — a `Shift2`-state machine: clear (`false`, move left), step left (no write), set
  (`true`, in place), halt.
* **`shiftLeft2_run`** — `run shiftLeft2 3 c = ⟨done, c.hd - 2, writeAt (writeAt c.tp c.hd false)
  (c.hd - 2) true⟩`.
* **`shiftLeft2_sets_new`** — the marker is now at `c.hd - 2` (the previous sim cell's marker).
* **`shiftLeft2_clears_old`** (needs `1 ≤ c.hd`) — the old marker at `c.hd` is gone.
* **`shiftLeft2_preserves`** — every other cell (including the skipped data cell `c.hd - 1`) is
  unchanged.

With brick 11 this gives bidirectional two-track simulated head motion.

## Honest scope

Completes the two-track "move the simulated head" primitive (both directions).  What remains for
`uStepOnTape`: the rule-lookup scan and the reset-to-0 per-step wrapper; then the lazy-delay diagonal.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveLeft2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveRight2 (Shift2)
open PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite (writeAt_getD_self)
open PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift (writeAt_getD_of_ne)

/-- **The two-track marker-shift-left machine.**  Clear the marker (move left), step left over the data
cell, set the new marker two cells back, halt. -/
def shiftLeft2 : Machine where
  State := Shift2
  fin := inferInstance
  dec := inferInstance
  start := Shift2.clr
  halt := fun s => match s with | .done => true | _ => false
  δ := fun s _ => match s with
    | .clr => (Shift2.mid, some false, (0 : Move))
    | .mid => (Shift2.setm, none, (0 : Move))
    | .setm => (Shift2.done, some true, (2 : Move))
    | .done => (Shift2.done, none, (2 : Move))
  accept := fun _ => false

theorem shiftLeft2_step_active {c : Cfg shiftLeft2} (hne : shiftLeft2.halt c.st = false) :
    step shiftLeft2 c = ⟨(shiftLeft2.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (shiftLeft2.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (shiftLeft2.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem shiftLeft2_step_clr {c : Cfg shiftLeft2} (hs : c.st = Shift2.clr) :
    step shiftLeft2 c = ⟨Shift2.mid, c.hd - 1, writeAt c.tp c.hd false⟩ := by
  rw [shiftLeft2_step_active (by rw [hs]; rfl), hs]; rfl

theorem shiftLeft2_step_mid {c : Cfg shiftLeft2} (hs : c.st = Shift2.mid) :
    step shiftLeft2 c = ⟨Shift2.setm, c.hd - 1, c.tp⟩ := by
  rw [shiftLeft2_step_active (by rw [hs]; rfl), hs]; rfl

theorem shiftLeft2_step_setm {c : Cfg shiftLeft2} (hs : c.st = Shift2.setm) :
    step shiftLeft2 c = ⟨Shift2.done, c.hd, writeAt c.tp c.hd true⟩ := by
  rw [shiftLeft2_step_active (by rw [hs]; rfl), hs]; rfl

/-- **The shift-by-two-left runs (proved).**  Three steps: clear `c.hd`, step over `c.hd - 1`, set
`c.hd - 2`. -/
theorem shiftLeft2_run (c : Cfg shiftLeft2) (hs : c.st = Shift2.clr) :
    run shiftLeft2 3 c
      = ⟨Shift2.done, c.hd - 2, writeAt (writeAt c.tp c.hd false) (c.hd - 2) true⟩ := by
  show step shiftLeft2 (step shiftLeft2 (step shiftLeft2 c)) = _
  rw [shiftLeft2_step_clr hs,
    shiftLeft2_step_mid (c := ⟨Shift2.mid, c.hd - 1, writeAt c.tp c.hd false⟩) rfl,
    shiftLeft2_step_setm (c := ⟨Shift2.setm, c.hd - 1 - 1, writeAt c.tp c.hd false⟩) rfl,
    show c.hd - 1 - 1 = c.hd - 2 from by omega]

/-- **The new marker is set (proved).**  After the shift, `c.hd - 2` holds the marker. -/
theorem shiftLeft2_sets_new (c : Cfg shiftLeft2) (hs : c.st = Shift2.clr) :
    (run shiftLeft2 3 c).tp.getD (c.hd - 2) false = true := by
  rw [shiftLeft2_run c hs]
  exact writeAt_getD_self (writeAt c.tp c.hd false) (c.hd - 2) true

/-- **The old marker is cleared (proved).**  After the shift, `c.hd` no longer holds the marker
(needs `1 ≤ c.hd`). -/
theorem shiftLeft2_clears_old (c : Cfg shiftLeft2) (hs : c.st = Shift2.clr) (hpos : 1 ≤ c.hd) :
    (run shiftLeft2 3 c).tp.getD c.hd false = false := by
  rw [shiftLeft2_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd - 2) c.hd true (by omega)]
  exact writeAt_getD_self c.tp c.hd false

/-- **The rest of the tape is untouched (proved).**  Every cell other than `c.hd` and `c.hd - 2` —
including the skipped data cell `c.hd - 1` — is unchanged. -/
theorem shiftLeft2_preserves (c : Cfg shiftLeft2) (hs : c.st = Shift2.clr)
    (q : ℕ) (hq1 : q ≠ c.hd) (hq2 : q ≠ c.hd - 2) :
    (run shiftLeft2 3 c).tp.getD q false = c.tp.getD q false := by
  rw [shiftLeft2_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd - 2) q true (by omega),
    writeAt_getD_of_ne c.tp c.hd q false (by omega)]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveLeft2

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveLeft2.shiftLeft2_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveLeft2.shiftLeft2_clears_old
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveLeft2.shiftLeft2_preserves

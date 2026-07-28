import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineMarkerShift

/-!
# Head-move construction, brick 11: two-track simulated head-move right (`shiftRight2`)

In the two-track layout (brick 9) each simulated cell is two physical cells `[data, marker]`, so moving
the simulated head one cell right moves the head-marker by **two** physical cells: from cell `p =
2·hd+1` (the marker of sim cell `hd`) to `p + 2 = 2·(hd+1)+1` (the marker of sim cell `hd+1`).  The
brick-5 `shiftRight` moves the marker by one — correct for a single-track marker, but off by a factor of
two here.  This brick is the two-track-correct move: `shiftRight2` clears the marker at `p`, steps right
over the intervening data cell, and sets the marker at `p + 2`.

It reuses the write lemmas (`writeAt_getD_self`, `writeAt_getD_of_ne`) from brick 5.

## What is proved

* **`shiftRight2`** — a four-state machine (`clr → mid → setm → done`): clear (`false`, move right),
  step right (no write, over the data cell), set (`true`, in place), halt.
* **`shiftRight2_run`** — `run shiftRight2 3 c = ⟨done, c.hd + 2, writeAt (writeAt c.tp c.hd false)
  (c.hd + 2) true⟩`.
* **`shiftRight2_sets_new`** — the marker is now at `c.hd + 2` (the next sim cell's marker).
* **`shiftRight2_clears_old`** — the old marker at `c.hd` is gone.
* **`shiftRight2_preserves`** — every other cell (including the skipped data cell `c.hd + 1`) is
  unchanged.

## Honest scope

The two-track-correct "move the simulated head right".  What remains for `uStepOnTape`: the two-track
move-left (mirror), the rule-lookup scan, and the reset-to-0 per-step wrapper; then the lazy-delay
diagonal.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveRight2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite (writeAt_getD_self)
open PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift (writeAt_getD_of_ne)

/-- Control states of `shiftRight2`: clear, step over the data cell, set, done. -/
inductive Shift2 where
  | clr : Shift2
  | mid : Shift2
  | setm : Shift2
  | done : Shift2
  deriving DecidableEq

instance : Fintype Shift2 :=
  ⟨{.clr, .mid, .setm, .done}, fun x => by cases x <;> decide⟩

/-- **The two-track marker-shift-right machine.**  Clear the marker (move right), step right over the
data cell, set the new marker two cells along, halt. -/
def shiftRight2 : Machine where
  State := Shift2
  fin := inferInstance
  dec := inferInstance
  start := Shift2.clr
  halt := fun s => match s with | .done => true | _ => false
  δ := fun s _ => match s with
    | .clr => (Shift2.mid, some false, (1 : Move))
    | .mid => (Shift2.setm, none, (1 : Move))
    | .setm => (Shift2.done, some true, (2 : Move))
    | .done => (Shift2.done, none, (2 : Move))
  accept := fun _ => false

theorem shiftRight2_step_active {c : Cfg shiftRight2} (hne : shiftRight2.halt c.st = false) :
    step shiftRight2 c = ⟨(shiftRight2.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (shiftRight2.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (shiftRight2.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem shiftRight2_step_clr {c : Cfg shiftRight2} (hs : c.st = Shift2.clr) :
    step shiftRight2 c = ⟨Shift2.mid, c.hd + 1, writeAt c.tp c.hd false⟩ := by
  rw [shiftRight2_step_active (by rw [hs]; rfl), hs]; rfl

theorem shiftRight2_step_mid {c : Cfg shiftRight2} (hs : c.st = Shift2.mid) :
    step shiftRight2 c = ⟨Shift2.setm, c.hd + 1, c.tp⟩ := by
  rw [shiftRight2_step_active (by rw [hs]; rfl), hs]; rfl

theorem shiftRight2_step_setm {c : Cfg shiftRight2} (hs : c.st = Shift2.setm) :
    step shiftRight2 c = ⟨Shift2.done, c.hd, writeAt c.tp c.hd true⟩ := by
  rw [shiftRight2_step_active (by rw [hs]; rfl), hs]; rfl

/-- **The shift-by-two runs (proved).**  Three steps: clear `c.hd`, step over `c.hd + 1`, set
`c.hd + 2`. -/
theorem shiftRight2_run (c : Cfg shiftRight2) (hs : c.st = Shift2.clr) :
    run shiftRight2 3 c
      = ⟨Shift2.done, c.hd + 2, writeAt (writeAt c.tp c.hd false) (c.hd + 2) true⟩ := by
  show step shiftRight2 (step shiftRight2 (step shiftRight2 c)) = _
  rw [shiftRight2_step_clr hs,
    shiftRight2_step_mid (c := ⟨Shift2.mid, c.hd + 1, writeAt c.tp c.hd false⟩) rfl,
    shiftRight2_step_setm (c := ⟨Shift2.setm, c.hd + 1 + 1, writeAt c.tp c.hd false⟩) rfl]

/-- **The new marker is set (proved).**  After the shift, `c.hd + 2` holds the marker. -/
theorem shiftRight2_sets_new (c : Cfg shiftRight2) (hs : c.st = Shift2.clr) :
    (run shiftRight2 3 c).tp.getD (c.hd + 2) false = true := by
  rw [shiftRight2_run c hs]
  exact writeAt_getD_self (writeAt c.tp c.hd false) (c.hd + 2) true

/-- **The old marker is cleared (proved).**  After the shift, `c.hd` no longer holds the marker. -/
theorem shiftRight2_clears_old (c : Cfg shiftRight2) (hs : c.st = Shift2.clr) :
    (run shiftRight2 3 c).tp.getD c.hd false = false := by
  rw [shiftRight2_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd + 2) c.hd true (by omega)]
  exact writeAt_getD_self c.tp c.hd false

/-- **The rest of the tape is untouched (proved).**  Every cell other than `c.hd` and `c.hd + 2` —
including the skipped data cell `c.hd + 1` — is unchanged. -/
theorem shiftRight2_preserves (c : Cfg shiftRight2) (hs : c.st = Shift2.clr)
    (q : ℕ) (hq1 : q ≠ c.hd) (hq2 : q ≠ c.hd + 2) :
    (run shiftRight2 3 c).tp.getD q false = c.tp.getD q false := by
  rw [shiftRight2_run c hs,
    writeAt_getD_of_ne (writeAt c.tp c.hd false) (c.hd + 2) q true (by omega),
    writeAt_getD_of_ne c.tp c.hd q false (by omega)]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveRight2

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveRight2.shiftRight2_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveRight2.shiftRight2_sets_new
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineMoveRight2.shiftRight2_preserves

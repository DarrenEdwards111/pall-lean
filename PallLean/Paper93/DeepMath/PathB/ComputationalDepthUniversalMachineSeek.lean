import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineHeadMove

/-!
# Head-move construction, brick 4: the data-dependent seek (marker scan)

The universal control must move the physical head to the *simulated head position* — a quantity that
is DATA, not known to the finite control.  The textbook realisation is a unary counter that consumes
and restores tape marks, whose correctness proof has to track an evolving tape.  This brick takes the
clean route instead: represent the simulated head as a **position marker** — a single `true` in a run
of `false`s at the head's position — so that "seek to the simulated head" is simply *scan right to the
first `true`*.  That is write-free, data-dependent, and proved by the same induction as the field-walk
(brick 1).  It answers "how do you seek by data at all" without any tape mutation.

## What is proved

* **`scanToTrue`** — a two-state `ComposableMachine` (mirror of `scanUnary`): in the scanning state it
  reads the cell under the head; a `false` moves the head one cell right and keeps scanning, a `true`
  halts in place (the marker is found).  No writes — the tape is untouched.
* **`scanToTrue_step_false` / `scanToTrue_step_true`** — the two local transitions, computed.
* **`scanToTrue_run`** (the seek invariant, by induction): from the scanning state, if the `n` cells
  ahead are `false` and the `n`-th is `true`, then after `n + 1` steps the machine is halted with the
  head advanced by exactly `n` onto the marker, tape unchanged:
  `run scanToTrue (n+1) c = ⟨true, c.hd + n, c.tp⟩`.
* **`scanToTrue_run_halted` / `scanToTrue_run_stable`** — genuinely halted on the marker; stays.
* **`scanToTrue_seeks`** (the payoff): on any tape `pre ++ replicate n false ++ (true :: post)` with
  the head at `|pre|`, the machine seeks to the marker at `|pre| + n` — the data-dependent seek to a
  head marked at (unknown-to-the-control) distance `n`, no mutation.

## Honest scope

This is the clean resolution of the seek crux at the primitive level: seeking to a marked position is
a write-free scan, provable like the field-walk, with none of the counter/mutation machinery.
Assembling the full `uStepOnTape` control on this basis still needs: the marked-head config layout (so
the simulated head is stored as a marker, and a simulated left/right move shifts the marker via the
brick-3 writes), rule lookup, and sequencing; then the lazy-delay diagonal (brick 5).  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineSeek

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial

/-- **The marker-seek machine.**  A fixed-control `ComposableMachine`; the state is a "found?" bit
(`false` = still scanning, `true` = found/halted).  In the scanning state it reads the cell under the
head: `false` ⇒ move one cell right, keep scanning; `true` ⇒ stop in place on the marker.  No writes —
the tape is never modified. -/
def scanToTrue : Machine where
  State := Bool
  fin := inferInstance
  dec := inferInstance
  start := false
  halt := fun s => s
  δ := fun _ b => if b then (true, none, (2 : Move)) else (false, none, (1 : Move))
  accept := fun s => s

/-- `run scanToTrue (t+1) c = run scanToTrue t (step scanToTrue c)` — step at the front, for the
seek induction. -/
theorem scanToTrue_run_succ_head (t : ℕ) (c : Cfg scanToTrue) :
    run scanToTrue (t + 1) c = run scanToTrue t (step scanToTrue c) :=
  Function.iterate_succ_apply (step scanToTrue) t c

/-- **Scanning step on a `false`.**  Moves the head one cell right and keeps scanning; tape untouched. -/
theorem scanToTrue_step_false {c : Cfg scanToTrue} (hs : c.st = false)
    (hb : c.tp.getD c.hd false = false) :
    step scanToTrue c = ⟨false, c.hd + 1, c.tp⟩ := by
  have hstep : step scanToTrue c
      = ⟨(scanToTrue.δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd (scanToTrue.δ c.st (c.tp.getD c.hd false)).2.2,
         (match (scanToTrue.δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
    unfold step
    rw [show scanToTrue.halt c.st = false from hs]
    rfl
  rw [hstep, hb]; rfl

/-- **Scanning step on a `true`.**  Stops in place on the marker; head does not move, tape untouched. -/
theorem scanToTrue_step_true {c : Cfg scanToTrue} (hs : c.st = false)
    (hb : c.tp.getD c.hd false = true) :
    step scanToTrue c = ⟨true, c.hd, c.tp⟩ := by
  have hstep : step scanToTrue c
      = ⟨(scanToTrue.δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd (scanToTrue.δ c.st (c.tp.getD c.hd false)).2.2,
         (match (scanToTrue.δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
    unfold step
    rw [show scanToTrue.halt c.st = false from hs]
    rfl
  rw [hstep, hb]; rfl

/-- **The seek invariant (proved).**  From the scanning state, if the `n` cells ahead of the head are
`false` and the `n`-th cell ahead is `true`, then after `n + 1` steps the machine is halted with the
head advanced by exactly `n` onto the marker and the tape unchanged. -/
theorem scanToTrue_run (n : ℕ) : ∀ (c : Cfg scanToTrue), c.st = false →
    (∀ i, i < n → c.tp.getD (c.hd + i) false = false) →
    c.tp.getD (c.hd + n) false = true →
    run scanToTrue (n + 1) c = ⟨true, c.hd + n, c.tp⟩ := by
  induction n with
  | zero =>
    intro c hs _ hmark
    rw [Nat.add_zero] at hmark
    rw [show run scanToTrue 1 c = step scanToTrue c from rfl, scanToTrue_step_true hs hmark]
    simp only [Nat.add_zero]
  | succ n ih =>
    intro c hs hfalse hmark
    have h0 : c.tp.getD c.hd false = false := by
      have := hfalse 0 (Nat.succ_pos n); rwa [Nat.add_zero] at this
    rw [scanToTrue_run_succ_head, scanToTrue_step_false hs h0]
    have hkey := ih ⟨false, c.hd + 1, c.tp⟩ rfl
      (fun i hi => by
        show c.tp.getD (c.hd + 1 + i) false = false
        have := hfalse (i + 1) (by omega)
        rwa [show c.hd + (i + 1) = c.hd + 1 + i from by omega] at this)
      (by
        show c.tp.getD (c.hd + 1 + n) false = true
        rwa [show c.hd + (n + 1) = c.hd + 1 + n from by omega] at hmark)
    rw [hkey]
    show (⟨true, c.hd + 1 + n, c.tp⟩ : Cfg scanToTrue) = ⟨true, c.hd + (n + 1), c.tp⟩
    rw [show c.hd + 1 + n = c.hd + (n + 1) from by omega]

/-- The seek genuinely halts on the marker. -/
theorem scanToTrue_run_halted (n : ℕ) (c : Cfg scanToTrue) (hs : c.st = false)
    (hfalse : ∀ i, i < n → c.tp.getD (c.hd + i) false = false)
    (hmark : c.tp.getD (c.hd + n) false = true) :
    scanToTrue.halt (run scanToTrue (n + 1) c).st = true := by
  rw [scanToTrue_run n c hs hfalse hmark]; rfl

/-- Having found the marker, the seek stays put at any later time. -/
theorem scanToTrue_run_stable (n : ℕ) (c : Cfg scanToTrue) (hs : c.st = false)
    (hfalse : ∀ i, i < n → c.tp.getD (c.hd + i) false = false)
    (hmark : c.tp.getD (c.hd + n) false = true)
    {T : ℕ} (hle : n + 1 ≤ T) :
    run scanToTrue T c = ⟨true, c.hd + n, c.tp⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [run_add, scanToTrue_run n c hs hfalse hmark]
  exact run_of_halted scanToTrue (by rfl) d

/-- **Payoff (proved): the data-dependent seek to a marked head.**  On any tape `pre ++ replicate n
false ++ (true :: post)` — a head marked at distance `n` (unknown to the control) — with the head at
`|pre|`, `scanToTrue` seeks to the marker at `|pre| + n`, tape unchanged.  No mutation, no counter. -/
theorem scanToTrue_seeks (pre post : List Bool) (n : ℕ) :
    run scanToTrue (n + 1) ⟨false, pre.length, pre ++ List.replicate n false ++ (true :: post)⟩
      = ⟨true, pre.length + n, pre ++ List.replicate n false ++ (true :: post)⟩ := by
  apply scanToTrue_run n ⟨false, pre.length, pre ++ List.replicate n false ++ (true :: post)⟩ rfl
  · intro i hi
    show (pre ++ List.replicate n false ++ (true :: post)).getD (pre.length + i) false = false
    simp only [List.append_assoc]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right pre.length i), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by rw [List.length_replicate]; exact hi),
      List.getElem?_replicate_of_lt hi]
    rfl
  · show (pre ++ List.replicate n false ++ (true :: post)).getD (pre.length + n) false = true
    simp only [List.append_assoc]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right pre.length n), Nat.add_sub_cancel_left,
      List.getElem?_append_right (by simp)]
    simp

end PallLean.Paper93.DeepMath.PathB.UniversalMachineSeek

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeek.scanToTrue_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeek.scanToTrue_seeks

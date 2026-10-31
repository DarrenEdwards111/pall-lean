import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineTapeStep

/-!
# Head-move construction, brick 1: the unary-field scanner as a real `ComposableMachine`

The tape functions (`uStepOnTape`, `tapeHalted`, `tapeAccepts`) are *functions on the tape*; to make
them a genuine `ComposableMachine` we must realise them as bounded head-move operations of a
fixed-control machine.  Every one of those functions begins by WALKING across the self-delimiting
tape to a field boundary — and because the encoding is unary (`encNat n = n` trues then a terminating
`false`), that walk is a single primitive: scan right over a run of `true`s, stop on the first
`false`.  This is `decNat` realised physically, on the actual `ComposableMachine` head.

This file builds that primitive — `scanUnary`, an honest two-state `ComposableMachine` — and proves it
correct against the real tape and the real encoding:

## What is proved

* **`scanUnary`** — a fixed-control machine, state = "stopped?" bit: in the scanning state it reads
  the cell under the head; a `true` moves the head one cell right and keeps scanning, a `false` halts
  in place.  No writes — the tape is never touched.
* **`scanUnary_step_true` / `scanUnary_step_false`** — the two local transitions, computed.
* **`scanUnary_run`** (the invariant, by induction): from the scanning state, if the `n` cells ahead
  are `true` and the `n`-th is `false`, then after `n + 1` steps the machine is halted with the head
  advanced by exactly `n` and *the tape unchanged*:
  `run scanUnary (n+1) c = ⟨true, c.hd + n, c.tp⟩`.
* **`scanUnary_run_halted` / `scanUnary_run_stable`** — it has genuinely halted, and stays put.
* **`encNat_eq_replicate`** — `encNat n = replicate n true ++ [false]` (the unary shape).
* **`scanUnary_parses_encNat`** (the payoff): on any tape `pre ++ encNat n ++ post` with the head at
  the start of the field (`|pre|`), the scanner walks to the field's terminator, ending halted at
  `|pre| + n`, tape unchanged — the physical `decNat`.

## Honest scope

This is one head-move primitive — the field-walk that every tape function starts with — realised as a
real fixed-control `ComposableMachine` and proved correct against the encoding, not a function stub.
It is the first brick of the tape-layout loop.  What remains for `DiagonalAgainstCanon`: compose this
scanner (with a unary counter and a local read/write) into the full `uStepOnTape` control, and the
lazy-delay diagonal (brick 5).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMove

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial

/-- **The unary-field scanner.**  A fixed-control `ComposableMachine`; the state is a "stopped?" bit
(`false` = still scanning, `true` = stopped/halted).  In the scanning state it reads the cell under
the head: `true` ⇒ move one cell right, keep scanning; `false` ⇒ stop in place.  No writes — the tape
is never modified. -/
def scanUnary : Machine where
  State := Bool
  fin := inferInstance
  dec := inferInstance
  start := false
  halt := fun s => s
  δ := fun _ b => if b then (false, none, (1 : Move)) else (true, none, (2 : Move))
  accept := fun s => s

/-- `run scanUnary (t+1) c = run scanUnary t (step scanUnary c)` — one step at the FRONT (the head of
the iteration), which is what the field-walk induction needs. -/
theorem scanUnary_run_succ_head (t : ℕ) (c : Cfg scanUnary) :
    run scanUnary (t + 1) c = run scanUnary t (step scanUnary c) :=
  Function.iterate_succ_apply (step scanUnary) t c

/-- **Scanning step on a `true`.**  Reading a `true` under the head moves the head one cell right and
keeps scanning; the tape is untouched. -/
theorem scanUnary_step_true {c : Cfg scanUnary} (hs : c.st = false)
    (hb : c.tp.getD c.hd false = true) :
    step scanUnary c = ⟨false, c.hd + 1, c.tp⟩ := by
  have hstep : step scanUnary c
      = ⟨(scanUnary.δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd (scanUnary.δ c.st (c.tp.getD c.hd false)).2.2,
         (match (scanUnary.δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
    unfold step
    rw [show scanUnary.halt c.st = false from hs]
    rfl
  rw [hstep, hb]; rfl

/-- **Scanning step on a `false`.**  Reading a `false` under the head stops the machine in place; the
head does not move and the tape is untouched. -/
theorem scanUnary_step_false {c : Cfg scanUnary} (hs : c.st = false)
    (hb : c.tp.getD c.hd false = false) :
    step scanUnary c = ⟨true, c.hd, c.tp⟩ := by
  have hstep : step scanUnary c
      = ⟨(scanUnary.δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd (scanUnary.δ c.st (c.tp.getD c.hd false)).2.2,
         (match (scanUnary.δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
    unfold step
    rw [show scanUnary.halt c.st = false from hs]
    rfl
  rw [hstep, hb]; rfl

/-- **The field-walk invariant (proved).**  From the scanning state, if the `n` cells ahead of the
head are `true` and the `n`-th cell ahead is `false`, then after `n + 1` steps the machine is halted
with the head advanced by exactly `n` and the tape unchanged. -/
theorem scanUnary_run (n : ℕ) : ∀ (c : Cfg scanUnary), c.st = false →
    (∀ i, i < n → c.tp.getD (c.hd + i) false = true) →
    c.tp.getD (c.hd + n) false = false →
    run scanUnary (n + 1) c = ⟨true, c.hd + n, c.tp⟩ := by
  induction n with
  | zero =>
    intro c hs _ hstop
    rw [Nat.add_zero] at hstop
    rw [show run scanUnary 1 c = step scanUnary c from rfl, scanUnary_step_false hs hstop]
    simp only [Nat.add_zero]
  | succ n ih =>
    intro c hs htrue hstop
    have h0 : c.tp.getD c.hd false = true := by
      have := htrue 0 (Nat.succ_pos n); rwa [Nat.add_zero] at this
    rw [scanUnary_run_succ_head, scanUnary_step_true hs h0]
    have hkey := ih ⟨false, c.hd + 1, c.tp⟩ rfl
      (fun i hi => by
        show c.tp.getD (c.hd + 1 + i) false = true
        have := htrue (i + 1) (by omega)
        rwa [show c.hd + (i + 1) = c.hd + 1 + i from by omega] at this)
      (by
        show c.tp.getD (c.hd + 1 + n) false = false
        rwa [show c.hd + (n + 1) = c.hd + 1 + n from by omega] at hstop)
    rw [hkey]
    show (⟨true, c.hd + 1 + n, c.tp⟩ : Cfg scanUnary) = ⟨true, c.hd + (n + 1), c.tp⟩
    rw [show c.hd + 1 + n = c.hd + (n + 1) from by omega]

/-- The scanner is genuinely halted after the walk. -/
theorem scanUnary_run_halted (n : ℕ) (c : Cfg scanUnary) (hs : c.st = false)
    (htrue : ∀ i, i < n → c.tp.getD (c.hd + i) false = true)
    (hstop : c.tp.getD (c.hd + n) false = false) :
    scanUnary.halt (run scanUnary (n + 1) c).st = true := by
  rw [scanUnary_run n c hs htrue hstop]; rfl

/-- Having halted, the scanner stays put at any later time. -/
theorem scanUnary_run_stable (n : ℕ) (c : Cfg scanUnary) (hs : c.st = false)
    (htrue : ∀ i, i < n → c.tp.getD (c.hd + i) false = true)
    (hstop : c.tp.getD (c.hd + n) false = false)
    {T : ℕ} (hle : n + 1 ≤ T) :
    run scanUnary T c = ⟨true, c.hd + n, c.tp⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [run_add, scanUnary_run n c hs htrue hstop]
  exact run_of_halted scanUnary (by rfl) d

/-- **The unary shape (proved).**  `encNat n = replicate n true ++ [false]`. -/
theorem encNat_eq_replicate (n : ℕ) : encNat n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encNat, ih, List.replicate_succ, List.cons_append]

/-- **The payoff (proved): the scanner physically realises `decNat`.**  On any tape
`pre ++ encNat n ++ post`, with the head at the start of the field (`|pre|`) and the machine
scanning, running `n + 1` steps walks the head to the field's terminator: halted at position
`|pre| + n`, the tape unchanged. -/
theorem scanUnary_parses_encNat (pre post : List Bool) (n : ℕ) :
    run scanUnary (n + 1) ⟨false, pre.length, pre ++ encNat n ++ post⟩
      = ⟨true, pre.length + n, pre ++ encNat n ++ post⟩ := by
  apply scanUnary_run n ⟨false, pre.length, pre ++ encNat n ++ post⟩ rfl
  · intro i hi
    show (pre ++ encNat n ++ post).getD (pre.length + i) false = true
    rw [encNat_eq_replicate]
    simp only [List.append_assoc]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right pre.length i), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by rw [List.length_replicate]; exact hi),
      List.getElem?_replicate_of_lt hi]
    rfl
  · show (pre ++ encNat n ++ post).getD (pre.length + n) false = false
    rw [encNat_eq_replicate]
    simp only [List.append_assoc]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right pre.length n), Nat.add_sub_cancel_left,
      List.getElem?_append_right (by simp)]
    simp

end PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMove

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMove.scanUnary_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMove.scanUnary_parses_encNat

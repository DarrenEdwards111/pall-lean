import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinLookupMachine

/-!
# Cook–Levin M1, step (1b′) — data-dependent WRITE (the atomic marking operation)

The two-pointer variable→value lookup needs to *mark* tape cells.  Pressure-testing surfaced a genuine model
constraint: the tape is **Boolean** (two symbols), so a mark cannot be a fresh third symbol — the classic
two-pointer must instead *consume/shift*, making a full `read a_v` an `O(v²)`/`O(nv)` shift construction.

This file builds the atomic operation underneath any marking: a **data-dependent write**.  `markMachine` seeks to
the first `false` (a data-dependent position `k`) and *writes* `true` there — the first machine here to use the
model's write capability.  `mark_correct`: the output tape is exactly `writeAt x k true`; `mark_present`: position
`k` now reads `true`.

Honest scope: this is one atomic mark.  The full `read a_v` loop (iterate: locate the next counter cell, consume
it, advance the assignment pointer by one, bounce) is the remaining `O(v²)` shift construction, scoped in
`SCOPE_COOKLEVIN.md`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinMarkMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEvalMachine (getD_pad)
open PallLean.Paper93.DeepMath.PathB.CookLevinLookupMachine (false_exists firstFalse)

/-- Control: `State = Fin 2` — phase `0`=seek, `1`=halted. -/
def markMachine : Machine where
  State := Fin 2
  fin := inferInstance
  dec := inferInstance
  start := 0
  halt := fun s => decide (s = 1)
  δ := fun s b =>
    if s = 0 then (if b then (0, none, 1) else (1, some true, 2)) else (1, none, 2)
  accept := fun _ => false

/-- Seeking over a `true`: advance, no write. -/
theorem step_seek_true {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step markMachine ⟨(0 : Fin 2), p, x⟩ = ⟨(0 : Fin 2), p + 1, x⟩ := by
  simp only [step, markMachine, h, moveHead]; rfl

/-- Reaching the first `false`: WRITE `true` here and halt. -/
theorem step_mark {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step markMachine ⟨(0 : Fin 2), p, x⟩ = ⟨(1 : Fin 2), p, writeAt x p true⟩ := by
  simp only [step, markMachine, h, moveHead]; rfl

/-- **Walk invariant.**  Over the leading `true`s, after `j` steps the head is at `j` and the tape is unchanged
(no writes happen until the mark). -/
theorem run_seek (x : List Bool) (j : ℕ) (hj : ∀ i < j, x.getD i false = true) :
    run markMachine j (init markMachine x) = ⟨(0 : Fin 2), j, x⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : ∀ i < j, x.getD i false = true := fun i hi => hj i (Nat.lt_succ_of_lt hi)
    have hflag : x.getD j false = true := hj j (Nat.lt_succ_self j)
    rw [run_succ, ih hj', step_seek_true hflag]

/-- **Marking is correct.**  After `firstFalse+1` steps the machine has written `true` at the data-dependent
position `firstFalse x`; the output tape is exactly `writeAt x (firstFalse x) true`, and it is halted. -/
theorem mark_correct (x : List Bool) :
    run markMachine (firstFalse x + 1) (init markMachine x)
      = ⟨(1 : Fin 2), firstFalse x, writeAt x (firstFalse x) true⟩ := by
  have hk : x.getD (firstFalse x) false = false := Nat.find_spec (false_exists x)
  have hmin : ∀ i < firstFalse x, x.getD i false = true :=
    fun i hi => by simpa using Nat.find_min (false_exists x) hi
  rw [run_succ, run_seek x (firstFalse x) hmin, step_mark hk]

/-- The mark is present: position `firstFalse x` of the output tape reads `true`. -/
theorem mark_present (x : List Bool) :
    (run markMachine (firstFalse x + 1) (init markMachine x)).tp.getD (firstFalse x) false = true := by
  rw [mark_correct]
  show (writeAt x (firstFalse x) true).getD (firstFalse x) false = true
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self]
  · rfl
  · rw [List.length_append, List.length_replicate]; omega

/-- The machine halts (`phase 1`) at the mark. -/
theorem mark_halts (x : List Bool) :
    markMachine.halt (run markMachine (firstFalse x + 1) (init markMachine x)).st = true := by
  rw [mark_correct]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinMarkMachine

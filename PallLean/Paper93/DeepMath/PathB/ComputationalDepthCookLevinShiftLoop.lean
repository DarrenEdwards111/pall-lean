import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinMarkMachine

/-!
# Cook–Levin M1, step (1b″) — an iterated-write loop with an evolving-tape invariant

Toward the full two-pointer `read a_v`.  Every machine so far either never wrote (`satAnd`/`satCNF`/`readAtUnary`)
or wrote exactly once (`markMachine`).  A shift loop writes at *every* step, so its correctness needs a genuinely
new technique: a run-invariant over the **evolving tape** (the tape at step `j` is not the input `x`, but `x`
transformed by the first `j` writes).

This file builds that technique on the counter-consumption phase: `clearCounter` walks over the leading `true`s
(the unary counter `1ᵏ`) writing `false` over each, halting at the first `false`.  The invariant
`run_clear : run clearCounter j (init x) = ⟨seek, j, zeroPrefix x j⟩` tracks the tape as `zeroPrefix x j` — `x`
with its first `j` cells zeroed — and is proved with the reusable tape lemmas `writeAt_getD_ne`/`_self`.
`clear_correct`: the counter is consumed to `zeroPrefix x (firstFalse x)`; `zeroPrefix_getD_lt`/`_ge` characterize
it exactly (cleared cells read `false`, the rest are unchanged).

Honest scope: this is the counter-consumption phase and the evolving-tape *proof technique* the full loop needs.
The full `read a_v` also advances an assignment pointer in tandem and bounces — the `O(v·n)` shift with Boolean-tape
boundary handling — still to build, scoped in `SCOPE_COOKLEVIN.md`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinLookupMachine (false_exists firstFalse)

/-! ## Reusable tape lemmas -/

/-- Appending `false` padding does not change any `getD`. -/
theorem getD_append_repl (l : List Bool) (m p : ℕ) :
    (l ++ List.replicate m false).getD p false = l.getD p false := by
  rcases lt_or_ge p l.length with hp | hp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hp, ← List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hp, List.getElem?_replicate,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none hp]
    split <;> rfl

/-- Writing at `q` leaves `getD` at any `p ≠ q` unchanged. -/
theorem writeAt_getD_ne {l : List Bool} {p q : ℕ} {w : Bool} (h : p ≠ q) :
    (writeAt l q w).getD p false = l.getD p false := by
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h), ← List.getD_eq_getElem?_getD]
  exact getD_append_repl l _ p

/-- Writing `w` at `q` makes `getD q` read `w`. -/
theorem writeAt_getD_self (l : List Bool) (q : ℕ) (w : Bool) :
    (writeAt l q w).getD q false = w := by
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self]
  · rfl
  · rw [List.length_append, List.length_replicate]; omega

/-! ## `zeroPrefix` and the evolving tape -/

/-- `x` with its first `j` cells overwritten by `false`. -/
def zeroPrefix (x : List Bool) : ℕ → List Bool
  | 0 => x
  | j + 1 => writeAt (zeroPrefix x j) j false

/-- Cells at or beyond the zeroed prefix are unchanged. -/
theorem zeroPrefix_getD_ge (x : List Bool) (j p : ℕ) (h : j ≤ p) :
    (zeroPrefix x j).getD p false = x.getD p false := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [zeroPrefix]
    rw [writeAt_getD_ne (show p ≠ j by omega)]
    exact ih (by omega)

/-- Cells inside the zeroed prefix read `false`. -/
theorem zeroPrefix_getD_lt (x : List Bool) (j p : ℕ) (h : p < j) :
    (zeroPrefix x j).getD p false = false := by
  induction j with
  | zero => omega
  | succ j ih =>
    simp only [zeroPrefix]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · rw [writeAt_getD_ne (show p ≠ j by omega)]; exact ih hlt
    · subst heq; exact writeAt_getD_self _ _ _

/-! ## The counter-consumption loop -/

/-- Control: `State = Fin 2` — phase `0`=clearing, `1`=halted. -/
def clearCounter : Machine where
  State := Fin 2
  fin := inferInstance
  dec := inferInstance
  start := 0
  halt := fun s => decide (s = 1)
  δ := fun s b =>
    if s = 0 then (if b then (0, some false, 1) else (1, none, 2)) else (1, none, 2)
  accept := fun _ => false

/-- Clearing a counter cell: overwrite `true` with `false`, advance. -/
theorem step_clear_true {p : ℕ} {x' : List Bool} (h : x'.getD p false = true) :
    step clearCounter ⟨(0 : Fin 2), p, x'⟩ = ⟨(0 : Fin 2), p + 1, writeAt x' p false⟩ := by
  simp only [step, clearCounter, h, moveHead]; rfl

/-- Reaching the separator: halt, no write. -/
theorem step_clear_false {p : ℕ} {x' : List Bool} (h : x'.getD p false = false) :
    step clearCounter ⟨(0 : Fin 2), p, x'⟩ = ⟨(1 : Fin 2), p, x'⟩ := by
  simp only [step, clearCounter, h, moveHead]; rfl

/-- **Evolving-tape invariant.**  After `j` steps the head is at `j` and the tape is `zeroPrefix x j` — the input
with its first `j` cells consumed to `false`. -/
theorem run_clear (x : List Bool) (j : ℕ) (hj : ∀ i < j, x.getD i false = true) :
    run clearCounter j (init clearCounter x) = ⟨(0 : Fin 2), j, zeroPrefix x j⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : ∀ i < j, x.getD i false = true := fun i hi => hj i (Nat.lt_succ_of_lt hi)
    have hflag : x.getD j false = true := hj j (Nat.lt_succ_self j)
    have hread : (zeroPrefix x j).getD j false = true := by
      rw [zeroPrefix_getD_ge x j j (le_refl _)]; exact hflag
    rw [run_succ, ih hj', step_clear_true hread]
    simp only [zeroPrefix]

/-- **The loop consumes the counter.**  After `firstFalse+1` steps the leading `true`s have all been overwritten
by `false`; the tape is `zeroPrefix x (firstFalse x)`, and the machine is halted. -/
theorem clear_correct (x : List Bool) :
    run clearCounter (firstFalse x + 1) (init clearCounter x)
      = ⟨(1 : Fin 2), firstFalse x, zeroPrefix x (firstFalse x)⟩ := by
  have hk : x.getD (firstFalse x) false = false := Nat.find_spec (false_exists x)
  have hmin : ∀ i < firstFalse x, x.getD i false = true :=
    fun i hi => by simpa using Nat.find_min (false_exists x) hi
  have hread : (zeroPrefix x (firstFalse x)).getD (firstFalse x) false = false := by
    rw [zeroPrefix_getD_ge x (firstFalse x) (firstFalse x) (le_refl _)]; exact hk
  rw [run_succ, run_clear x (firstFalse x) hmin, step_clear_false hread]

end PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop

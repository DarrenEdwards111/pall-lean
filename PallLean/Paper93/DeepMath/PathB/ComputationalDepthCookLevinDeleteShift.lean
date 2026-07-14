import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinShiftLoop

/-!
# Cook–Levin M1, step (1b‴) — the inner delete/left-shift pass

The two-pointer `read a_v` deletes cells (shift the suffix left).  Left-shift genuinely needs a head **bounce**: a
single head cannot read cell `p+1` and write cell `p` in one step.  The clean scheme is three steps per cell —
`FETCH` (skip the current cell, move right to the source), `GRAB` (read the source, carry it, move left to the
destination), `WRITE` (write the carry, move right) — carrying one bit in the finite control and rewriting the tape
every third step (the evolving-tape technique from `clearCounter`).

Built as a **run-invariant** (`run_shift`): a component inside `read a_v` needs no halting of its own, only a proven
per-`3k`-step result.  `run_shift`: `run shiftMachine (3k) ⟨FETCH, q, x⟩ = ⟨FETCH, q+k, lsTape x q k⟩`, where
`lsTape x q k` is `x` with positions `[q, q+k)` left-shifted.  `lsTape_shifted`: those positions now hold the
right-neighbour's original value — the delete is correct.

Honest scope: this is the inner shift pass.  The outer `v`-round loop that invokes it (consume a counter cell,
delete `a_0`, repeat, then read `a_v`) with an `O(v·n)` clock and top-level halting is the remaining glue, scoped
in `SCOPE_COOKLEVIN.md §5`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinDeleteShift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop (writeAt_getD_ne writeAt_getD_self)

/-- Control: `State = Fin 3 × Bool` — phase `0`=FETCH, `1`=GRAB, `2`=WRITE; paired with the carried bit. -/
def shiftMachine : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun _ => false
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2), none, 1)
    else if s.1 = 1 then ((2, b), none, 0)
    else ((0, s.2), some s.2, 1)
  accept := fun _ => false

/-- FETCH: skip the current (destination) cell, move right to the source. -/
theorem step_fetch {c : Bool} {p : ℕ} {tape : List Bool} :
    step shiftMachine ⟨(0, c), p, tape⟩ = ⟨(1, c), p + 1, tape⟩ := by
  simp only [step, shiftMachine, moveHead]; rfl

/-- GRAB: read the source cell into the carry, move left to the destination. -/
theorem step_grab {c : Bool} {p : ℕ} {tape : List Bool} :
    step shiftMachine ⟨(1, c), p + 1, tape⟩ = ⟨(2, tape.getD (p + 1) false), p, tape⟩ := by
  simp only [step, shiftMachine, moveHead]; rfl

/-- WRITE: write the carry at the destination, move right. -/
theorem step_write {c : Bool} {p : ℕ} {tape : List Bool} :
    step shiftMachine ⟨(2, c), p, tape⟩ = ⟨(0, c), p + 1, writeAt tape p c⟩ := by
  simp only [step, shiftMachine, moveHead]; rfl

/-- **One cell in three steps.**  From `FETCH` at `p`, three steps write `old[p+1]` into cell `p` and return to
`FETCH` at `p+1`, carrying `old[p+1]`. -/
theorem run_three {c : Bool} {p : ℕ} {tape : List Bool} :
    run shiftMachine 3 ⟨(0, c), p, tape⟩
      = ⟨(0, tape.getD (p + 1) false), p + 1, writeAt tape p (tape.getD (p + 1) false)⟩ := by
  rw [run_succ, run_succ, run_succ, run_zero, step_fetch, step_grab, step_write]

/-! ## The shifted tape and the run-invariant -/

/-- `x` with positions `[q, q+k)` left-shifted: each holds its right neighbour's original value. -/
def lsTape (x : List Bool) (q : ℕ) : ℕ → List Bool
  | 0 => x
  | k + 1 => writeAt (lsTape x q k) (q + k) (x.getD (q + k + 1) false)

/-- The carry after `3k` steps (irrelevant to the shift; tracked for a clean invariant). -/
def carryOf (x : List Bool) (q : ℕ) (c : Bool) : ℕ → Bool
  | 0 => c
  | k + 1 => x.getD (q + k + 1) false

/-- Positions at or beyond the shifted window are unchanged. -/
theorem lsTape_getD_ge (x : List Bool) (q p : ℕ) :
    ∀ k, q + k ≤ p → (lsTape x q k).getD p false = x.getD p false := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [lsTape]
    rw [writeAt_getD_ne (show p ≠ q + k by omega)]
    exact ih (by omega)

/-- **The shift is correct.**  Inside the window, each cell now holds its right neighbour's original value. -/
theorem lsTape_shifted (x : List Bool) (q p : ℕ) :
    ∀ k, q ≤ p → p < q + k → (lsTape x q k).getD p false = x.getD (p + 1) false := by
  intro k
  induction k with
  | zero => intro _ h2; omega
  | succ k ih =>
    intro h1 h2
    simp only [lsTape]
    rcases Nat.lt_or_ge p (q + k) with hlt | hge
    · rw [writeAt_getD_ne (show p ≠ q + k by omega)]; exact ih h1 hlt
    · have hp : p = q + k := by omega
      subst hp; rw [writeAt_getD_self]

/-- **Run-invariant.**  After `3k` steps from `FETCH` at `q`, the head is at `q+k` and the tape is `lsTape x q k`
(the window `[q, q+k)` left-shifted). -/
theorem run_shift (x : List Bool) (q : ℕ) (c : Bool) (k : ℕ) :
    run shiftMachine (3 * k) ⟨(0, c), q, x⟩ = ⟨(0, carryOf x q c k), q + k, lsTape x q k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 * k + 3 from by ring, run_add, ih, run_three,
      lsTape_getD_ge x q (q + k + 1) k (by omega)]
    simp only [carryOf, lsTape, Nat.add_succ]

end PallLean.Paper93.DeepMath.PathB.CookLevinDeleteShift

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinShiftLoop

/-!
# Cook–Levin M1 — the data-moving pair-shift (shift by two = delete a pair)

To delete a *pair* from the doubled encoding (`CookLevinDoubled`) the suffix must move left by **two** cells so the
pairing is preserved.  This is `DeleteShift`'s read-ahead bounce widened by one: skip two (`FETCH`, `FETCH2`), read
the source (`GRAB`), step back (`BACK`), write the carry (`WRITE`) — five steps per cell, `new[p] = old[p+2]`,
carried in the finite control on the evolving tape.

Built as a run-invariant (a component needs no halting): `run_shift2 : run pairShift (5k) ⟨FETCH, q, x⟩ =
⟨FETCH, q+k, lsTape2 x q k⟩`, where `lsTape2 x q k` is `x` with the window `[q, q+k)` shifted left by two.
`lsTape2_shifted` confirms the window now holds the value two cells to the right — the pair-delete is correct.

Honest scope: this is the data-moving pair-shift.  Welding it into a *halting* `read a_v` machine additionally needs
left/right sentinel markers (loop-head repositioning + dual shift termination), the v-round loop, and the
correctness link to `ReadAv.readAv_spec` — a multi-turn construction, not attempted here.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinPairShift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop (writeAt_getD_ne writeAt_getD_self)

/-- Control: `State = Fin 5 × Bool` — phases `0`=FETCH, `1`=FETCH2, `2`=GRAB, `3`=BACK, `4`=WRITE; carry bit. -/
def pairShift : Machine where
  State := Fin 5 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun _ => false
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2), none, 1)
    else if s.1 = 1 then ((2, s.2), none, 1)
    else if s.1 = 2 then ((3, b), none, 0)
    else if s.1 = 3 then ((4, s.2), none, 0)
    else ((0, s.2), some s.2, 1)
  accept := fun _ => false

/-- FETCH: skip the destination cell, move right. -/
theorem step_fetch {c : Bool} {p : ℕ} {tape : List Bool} :
    step pairShift ⟨(0, c), p, tape⟩ = ⟨(1, c), p + 1, tape⟩ := by
  simp only [step, pairShift, moveHead]; rfl

/-- FETCH2: skip a second cell, move right (to the source). -/
theorem step_fetch2 {c : Bool} {p : ℕ} {tape : List Bool} :
    step pairShift ⟨(1, c), p, tape⟩ = ⟨(2, c), p + 1, tape⟩ := by
  simp only [step, pairShift, moveHead]; rfl

/-- GRAB: read the source cell into the carry, step left. -/
theorem step_grab {c : Bool} {p : ℕ} {tape : List Bool} :
    step pairShift ⟨(2, c), p + 1, tape⟩ = ⟨(3, tape.getD (p + 1) false), p, tape⟩ := by
  simp only [step, pairShift, moveHead]; rfl

/-- BACK: step left to the destination. -/
theorem step_back {c : Bool} {p : ℕ} {tape : List Bool} :
    step pairShift ⟨(3, c), p + 1, tape⟩ = ⟨(4, c), p, tape⟩ := by
  simp only [step, pairShift, moveHead]; rfl

/-- WRITE: write the carry at the destination, move right. -/
theorem step_write {c : Bool} {p : ℕ} {tape : List Bool} :
    step pairShift ⟨(4, c), p, tape⟩ = ⟨(0, c), p + 1, writeAt tape p c⟩ := by
  simp only [step, pairShift, moveHead]; rfl

/-- **One cell in five steps.**  Five steps write `old[p+2]` into cell `p` and return to `FETCH` at `p+1`. -/
theorem run_five {c : Bool} {p : ℕ} {tape : List Bool} :
    run pairShift 5 ⟨(0, c), p, tape⟩
      = ⟨(0, tape.getD (p + 2) false), p + 1, writeAt tape p (tape.getD (p + 2) false)⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_succ, run_zero,
    step_fetch, step_fetch2, step_grab, step_back, step_write]

/-! ## The shifted tape and the run-invariant -/

/-- `x` with positions `[q, q+k)` shifted left by two: each holds the value two cells to its right. -/
def lsTape2 (x : List Bool) (q : ℕ) : ℕ → List Bool
  | 0 => x
  | k + 1 => writeAt (lsTape2 x q k) (q + k) (x.getD (q + k + 2) false)

/-- The carry after `5k` steps (irrelevant to the shift; tracked for a clean invariant). -/
def carry2 (x : List Bool) (q : ℕ) (c : Bool) : ℕ → Bool
  | 0 => c
  | k + 1 => x.getD (q + k + 2) false

/-- Positions at or beyond the shifted window are unchanged. -/
theorem lsTape2_getD_ge (x : List Bool) (q p : ℕ) :
    ∀ k, q + k ≤ p → (lsTape2 x q k).getD p false = x.getD p false := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [lsTape2]
    rw [writeAt_getD_ne (show p ≠ q + k by omega)]
    exact ih (by omega)

/-- **The pair-shift is correct.**  Inside the window, each cell now holds the value two cells to its right. -/
theorem lsTape2_shifted (x : List Bool) (q p : ℕ) :
    ∀ k, q ≤ p → p < q + k → (lsTape2 x q k).getD p false = x.getD (p + 2) false := by
  intro k
  induction k with
  | zero => intro _ h2; omega
  | succ k ih =>
    intro h1 h2
    simp only [lsTape2]
    rcases Nat.lt_or_ge p (q + k) with hlt | hge
    · rw [writeAt_getD_ne (show p ≠ q + k by omega)]; exact ih h1 hlt
    · have hp : p = q + k := by omega
      subst hp; rw [writeAt_getD_self]

/-- **Run-invariant.**  After `5k` steps from `FETCH` at `q`, the head is at `q+k` and the tape is `lsTape2 x q k`
(the window `[q, q+k)` shifted left by two). -/
theorem run_shift2 (x : List Bool) (q : ℕ) (c : Bool) (k : ℕ) :
    run pairShift (5 * k) ⟨(0, c), q, x⟩ = ⟨(0, carry2 x q c k), q + k, lsTape2 x q k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 5 * (k + 1) = 5 * k + 5 from by ring, run_add, ih, run_five,
      lsTape2_getD_ge x q (q + k + 2) k (by omega)]
    simp only [carry2, lsTape2, Nat.add_succ]

end PallLean.Paper93.DeepMath.PathB.CookLevinPairShift

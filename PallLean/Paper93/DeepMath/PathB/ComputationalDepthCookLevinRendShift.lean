import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinPairShift

/-!
# Cook–Levin M1, S5 — the REND-terminating pair-shift (structural core)

The delete-a-pair shift (`CookLevinPairShift`) is a run-lemma with no halting.  For the weld it must self-terminate
at the right-end marker `REND = 10`.  Detecting `10` is a *pair* property, so this machine is pair-based: it copies
the source pair `[d+2, d+3]` into the destination pair `[d, d+1]` (a left-shift by one pair) and, after writing,
**halts** if that pair was `REND` (`c₀=1, c₁=0`), else continues.

Eight phases per pair (head bounce across the 2-cell gap):
`FETCH1 FETCH2` (reach source) · `READLO READHI` (read the pair into the carry, step left) ·
`BACK1 BACK2` (reach dest) · `WRITELO WRITEHI` (write the pair; REND ⇒ halt, else continue).

This file: the machine, the eight step lemmas, and `run_eight_shift` — one non-REND pair copied in eight steps.
The `k`-pair evolving-tape invariant and the REND self-halt are the next chunk (mirroring how `run_shift2` followed
`run_five`).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinRendShift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Control: `State = Fin 9 × Bool × Bool` — phases `0..7` = FETCH1/FETCH2/READLO/READHI/BACK1/BACK2/WRITELO/
WRITEHI, `8` = halted; paired with the carried source pair `(c₀, c₁)`. -/
def rendShift : Machine where
  State := Fin 9 × Bool × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false, false)
  halt := fun s => decide (s.1 = 8)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, s.2.2), none, 1)
    else if s.1 = 1 then ((2, s.2.1, s.2.2), none, 1)
    else if s.1 = 2 then ((3, b, s.2.2), none, 1)
    else if s.1 = 3 then ((4, s.2.1, b), none, 0)
    else if s.1 = 4 then ((5, s.2.1, s.2.2), none, 0)
    else if s.1 = 5 then ((6, s.2.1, s.2.2), none, 0)
    else if s.1 = 6 then ((7, s.2.1, s.2.2), some s.2.1, 1)
    else if s.1 = 7 then
      (if s.2.1 && !s.2.2 then ((8, s.2.1, s.2.2), some s.2.2, 2)
       else ((0, s.2.1, s.2.2), some s.2.2, 1))
    else ((8, s.2.1, s.2.2), none, 2)
  accept := fun s => s.2.2

/-- FETCH1: skip the destination low cell. -/
theorem step_fetch1 {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step rendShift ⟨(0, c0, c1), p, tape⟩ = ⟨(1, c0, c1), p + 1, tape⟩ := by
  simp only [step, rendShift, moveHead]; rfl

/-- FETCH2: reach the source low cell. -/
theorem step_fetch2 {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step rendShift ⟨(1, c0, c1), p, tape⟩ = ⟨(2, c0, c1), p + 1, tape⟩ := by
  simp only [step, rendShift, moveHead]; rfl

/-- READLO: read the source low cell into `c₀`. -/
theorem step_readlo {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step rendShift ⟨(2, c0, c1), p, tape⟩ = ⟨(3, tape.getD p false, c1), p + 1, tape⟩ := by
  simp only [step, rendShift, moveHead]; rfl

/-- READHI: read the source high cell into `c₁`, step left. -/
theorem step_readhi {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step rendShift ⟨(3, c0, c1), p + 1, tape⟩ = ⟨(4, c0, tape.getD (p + 1) false), p, tape⟩ := by
  simp only [step, rendShift, moveHead]; rfl

/-- BACK1: step left toward the destination. -/
theorem step_back1 {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step rendShift ⟨(4, c0, c1), p + 1, tape⟩ = ⟨(5, c0, c1), p, tape⟩ := by
  simp only [step, rendShift, moveHead]; rfl

/-- BACK2: step left to the destination low cell. -/
theorem step_back2 {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step rendShift ⟨(5, c0, c1), p + 1, tape⟩ = ⟨(6, c0, c1), p, tape⟩ := by
  simp only [step, rendShift, moveHead]; rfl

/-- WRITELO: write `c₀` at the destination low cell. -/
theorem step_writelo {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step rendShift ⟨(6, c0, c1), p, tape⟩ = ⟨(7, c0, c1), p + 1, writeAt tape p c0⟩ := by
  simp only [step, rendShift, moveHead]; rfl

/-- WRITEHI (non-REND): write `c₁`, continue to the next pair. -/
theorem step_writehi_cont {c0 c1 : Bool} {p : ℕ} {tape : List Bool} (h : (c0 && !c1) = false) :
    step rendShift ⟨(7, c0, c1), p, tape⟩ = ⟨(0, c0, c1), p + 1, writeAt tape p c1⟩ := by
  simp only [step, rendShift, moveHead, h]; rfl

/-- WRITEHI (REND `10`): write `c₁`, halt. -/
theorem step_writehi_halt {c0 c1 : Bool} {p : ℕ} {tape : List Bool} (h : (c0 && !c1) = true) :
    step rendShift ⟨(7, c0, c1), p, tape⟩ = ⟨(8, c0, c1), p, writeAt tape p c1⟩ := by
  simp only [step, rendShift, moveHead, h]; rfl

/-- **One non-REND pair in eight steps.**  The source pair `old[d+2], old[d+3]` is written into `[d, d+1]`
(a left-shift by one pair), and control returns to `FETCH1` at `d+2`. -/
theorem run_eight_shift {c0 c1 : Bool} {d : ℕ} {tape : List Bool}
    (h : (tape.getD (d + 2) false && !(tape.getD (d + 3) false)) = false) :
    run rendShift 8 ⟨(0, c0, c1), d, tape⟩
      = ⟨(0, tape.getD (d + 2) false, tape.getD (d + 3) false), d + 2,
          writeAt (writeAt tape d (tape.getD (d + 2) false)) (d + 1) (tape.getD (d + 3) false)⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_zero,
    step_fetch1, step_fetch2, step_readlo, step_readhi, step_back1, step_back2, step_writelo,
    step_writehi_cont h]

end PallLean.Paper93.DeepMath.PathB.CookLevinRendShift

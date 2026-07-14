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
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop (writeAt_getD_ne)

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

/-! ## The k-pair invariant and the REND self-halt -/

/-- `x` with `k` pairs (from `q`) shifted left by one pair: pair `i` gets `old[q+2i+2], old[q+2i+3]`. -/
def rsTape (x : List Bool) (q : ℕ) : ℕ → List Bool
  | 0 => x
  | k + 1 =>
    writeAt (writeAt (rsTape x q k) (q + 2 * k) (x.getD (q + 2 * k + 2) false))
      (q + 2 * k + 1) (x.getD (q + 2 * k + 3) false)

/-- The carried pair after `k` pairs (irrelevant to the shift; tracked for a clean invariant). -/
def carryK (x : List Bool) (q : ℕ) (c0 c1 : Bool) : ℕ → Bool × Bool
  | 0 => (c0, c1)
  | k + 1 => (x.getD (q + 2 * k + 2) false, x.getD (q + 2 * k + 3) false)

/-- Positions at or beyond the shifted window are unchanged. -/
theorem rsTape_getD_ge (x : List Bool) (q p : ℕ) :
    ∀ k, q + 2 * k ≤ p → (rsTape x q k).getD p false = x.getD p false := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [rsTape]
    rw [writeAt_getD_ne (show p ≠ q + 2 * k + 1 by omega), writeAt_getD_ne (show p ≠ q + 2 * k by omega)]
    exact ih (by omega)

/-- One REND pair in eight steps: write it into the destination and halt (`phase 8`). -/
theorem run_eight_halt {c0 c1 : Bool} {d : ℕ} {tape : List Bool}
    (h : (tape.getD (d + 2) false && !(tape.getD (d + 3) false)) = true) :
    run rendShift 8 ⟨(0, c0, c1), d, tape⟩
      = ⟨(8, tape.getD (d + 2) false, tape.getD (d + 3) false), d + 1,
          writeAt (writeAt tape d (tape.getD (d + 2) false)) (d + 1) (tape.getD (d + 3) false)⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_zero,
    step_fetch1, step_fetch2, step_readlo, step_readhi, step_back1, step_back2, step_writelo,
    step_writehi_halt h]

/-- **k-pair invariant.**  While the first `k` source pairs are non-REND, after `8k` steps the head is at `q+2k`
and the tape is `rsTape x q k` (the window shifted left by one pair). -/
theorem run_shift_k (x : List Bool) (q : ℕ) (c0 c1 : Bool) (k : ℕ)
    (hnr : ∀ i < k, (x.getD (q + 2 * i + 2) false && !(x.getD (q + 2 * i + 3) false)) = false) :
    run rendShift (8 * k) ⟨(0, c0, c1), q, x⟩
      = ⟨(0, (carryK x q c0 c1 k).1, (carryK x q c0 c1 k).2), q + 2 * k, rsTape x q k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hnr' : ∀ i < k, (x.getD (q + 2 * i + 2) false && !(x.getD (q + 2 * i + 3) false)) = false :=
      fun i hi => hnr i (Nat.lt_succ_of_lt hi)
    have hk : (x.getD (q + 2 * k + 2) false && !(x.getD (q + 2 * k + 3) false)) = false :=
      hnr k (Nat.lt_succ_self k)
    have hge2 : (rsTape x q k).getD (q + 2 * k + 2) false = x.getD (q + 2 * k + 2) false :=
      rsTape_getD_ge x q (q + 2 * k + 2) k (by omega)
    have hge3 : (rsTape x q k).getD (q + 2 * k + 3) false = x.getD (q + 2 * k + 3) false :=
      rsTape_getD_ge x q (q + 2 * k + 3) k (by omega)
    rw [show 8 * (k + 1) = 8 * k + 8 from by ring, run_add, ih hnr',
      run_eight_shift (by rw [hge2, hge3]; exact hk), hge2, hge3]
    simp only [carryK, rsTape, Nat.mul_succ, Nat.add_assoc]

/-- **REND self-halt.**  If the first `K` pairs are non-REND and pair `K` is `REND = 10`, then after `8K+8` steps
the machine has copied `REND` into position and halted (`phase 8`) at `q+2K+1`. -/
theorem run_shift_halt (x : List Bool) (q : ℕ) (c0 c1 : Bool) (K : ℕ)
    (hnr : ∀ i < K, (x.getD (q + 2 * i + 2) false && !(x.getD (q + 2 * i + 3) false)) = false)
    (hrend : (x.getD (q + 2 * K + 2) false && !(x.getD (q + 2 * K + 3) false)) = true) :
    run rendShift (8 * K + 8) ⟨(0, c0, c1), q, x⟩
      = ⟨(8, x.getD (q + 2 * K + 2) false, x.getD (q + 2 * K + 3) false), q + 2 * K + 1,
          rsTape x q (K + 1)⟩ := by
  have hge2 : (rsTape x q K).getD (q + 2 * K + 2) false = x.getD (q + 2 * K + 2) false :=
    rsTape_getD_ge x q (q + 2 * K + 2) K (by omega)
  have hge3 : (rsTape x q K).getD (q + 2 * K + 3) false = x.getD (q + 2 * K + 3) false :=
    rsTape_getD_ge x q (q + 2 * K + 3) K (by omega)
  rw [run_add, run_shift_k x q c0 c1 K hnr, run_eight_halt (by rw [hge2, hge3]; exact hrend), hge2, hge3]
  simp only [rsTape]

/-- The REND-terminating shift is genuinely halted. -/
theorem rend_halted (x : List Bool) (q : ℕ) (c0 c1 : Bool) (K : ℕ)
    (hnr : ∀ i < K, (x.getD (q + 2 * i + 2) false && !(x.getD (q + 2 * i + 3) false)) = false)
    (hrend : (x.getD (q + 2 * K + 2) false && !(x.getD (q + 2 * K + 3) false)) = true) :
    rendShift.halt (run rendShift (8 * K + 8) ⟨(0, c0, c1), q, x⟩).st = true := by
  rw [run_shift_halt x q c0 c1 K hnr hrend]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinRendShift

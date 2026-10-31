import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinScanMarker
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinShiftLoop

/-!
# Cook–Levin M1 — the detectable-termination WRITE pass

`scanMarker` fixed the run-forever problem for a *read* scan.  A shift also *writes*, and the same fix applies:
process doubled pairs, writing as you go, and halt at the first marker (differing pair).  This file builds that
write+terminate core: `clearMachine` overwrites both cells of each data pair with `false` (keeping it a valid data
pair `00`) and **halts** at the first marker.

Because clearing one cell of a `11` pair would forge a marker (`10`/`01`), both cells must be cleared — a small
head bounce (write high, step left, write low) plus the evolving-tape technique from `clearCounter`.
`clear_halt`: on `encodeD bs` the machine clears all `bs.length` data pairs and halts at the terminating marker.

Honest scope: this is the detectable-termination *write* pass.  The full *data-moving* pair-shift (delete a pair,
copy the rest two cells left, halt at a marker) is a heavier multi-phase head-bounce that composes this write+halt
core with `DeleteShift`'s read-ahead; it remains.  This proves writes self-terminate at a detectable boundary.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinClearMarker

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop (writeAt_getD_ne)

/-- Control: `State = Fin 5 × Bool` — phases `0`=read-low, `1`=read-high, `2`=write-low, `3`=skip, `4`=halted;
paired with the stored low cell (to compare against the high cell). -/
def clearMachine : Machine where
  State := Fin 5 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 4)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then (if b = s.2 then ((2, s.2), some false, 0) else ((4, s.2), none, 2))
    else if s.1 = 2 then ((3, s.2), some false, 1)
    else if s.1 = 3 then ((0, s.2), none, 1)
    else ((4, s.2), none, 2)
  accept := fun s => s.2

/-- Read the low cell, store it, advance. -/
theorem step_readLo {s : Bool} {p : ℕ} {tape : List Bool} :
    step clearMachine ⟨(0, s), p, tape⟩ = ⟨(1, tape.getD p false), p + 1, tape⟩ := by
  simp only [step, clearMachine, moveHead]; rfl

/-- Read the high cell; equals the stored low cell (data pair) ⇒ clear this cell, step left to clear the low one. -/
theorem step_readHi_data {s : Bool} {p : ℕ} {tape : List Bool} (h : tape.getD (p + 1) false = s) :
    step clearMachine ⟨(1, s), p + 1, tape⟩ = ⟨(2, s), p, writeAt tape (p + 1) false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, clearMachine, moveHead, h]

/-- Read the high cell; differs from the stored low cell (marker) ⇒ halt. -/
theorem step_readHi_marker {s : Bool} {p : ℕ} {tape : List Bool} (h : tape.getD p false ≠ s) :
    step clearMachine ⟨(1, s), p, tape⟩ = ⟨(4, s), p, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, clearMachine, moveHead, h]

/-- Clear the low cell, advance. -/
theorem step_writeLo {s : Bool} {p : ℕ} {tape : List Bool} :
    step clearMachine ⟨(2, s), p, tape⟩ = ⟨(3, s), p + 1, writeAt tape p false⟩ := by
  simp only [step, clearMachine, moveHead]; rfl

/-- Skip to the next pair's low cell. -/
theorem step_skip {s : Bool} {p : ℕ} {tape : List Bool} :
    step clearMachine ⟨(3, s), p, tape⟩ = ⟨(0, s), p + 1, tape⟩ := by
  simp only [step, clearMachine, moveHead]; rfl

/-! ## The evolving tape and the self-halt at the marker -/

/-- `encodeD bs` with its first `j` data pairs cleared to `00`. -/
def clearedD (bs : List Bool) : ℕ → List Bool
  | 0 => encodeD bs
  | j + 1 => writeAt (writeAt (clearedD bs j) (2 * j + 1) false) (2 * j) false

/-- The stored low cell after `j` pairs (irrelevant to termination; tracked for a clean invariant). -/
def storedC (bs : List Bool) : ℕ → Bool
  | 0 => false
  | j + 1 => (encodeD bs).getD (2 * j) false

/-- Positions at or beyond the cleared window are unchanged (clearing pair `<j` touches positions `<2j`). -/
theorem clearedD_getD_ge (bs : List Bool) (p : ℕ) :
    ∀ j, 2 * j ≤ p → (clearedD bs j).getD p false = (encodeD bs).getD p false := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    simp only [clearedD]
    rw [writeAt_getD_ne (show p ≠ 2 * j by omega), writeAt_getD_ne (show p ≠ 2 * j + 1 by omega)]
    exact ih (by omega)

/-- Four steps clear one data pair (equal cells) to `00` and advance. -/
theorem run_four_data {s : Bool} {j : ℕ} {tape : List Bool}
    (heq : tape.getD (2 * j) false = tape.getD (2 * j + 1) false) :
    run clearMachine 4 ⟨(0, s), 2 * j, tape⟩
      = ⟨(0, tape.getD (2 * j) false), 2 * j + 2,
          writeAt (writeAt tape (2 * j + 1) false) (2 * j) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_readLo, step_readHi_data heq.symm,
    step_writeLo, step_skip]

/-- **Clear invariant.**  After `4j` steps the machine has cleared the first `j` data pairs and is reading the
low cell of pair `j`. -/
theorem run_clear (bs : List Bool) (j : ℕ) (hj : j ≤ bs.length) :
    run clearMachine (4 * j) (init clearMachine (encodeD bs))
      = ⟨(0, storedC bs j), 2 * j, clearedD bs j⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j ≤ bs.length := Nat.le_of_succ_le hj
    have heq : (clearedD bs j).getD (2 * j) false = (clearedD bs j).getD (2 * j + 1) false := by
      rw [clearedD_getD_ge bs (2 * j) j (le_refl _), clearedD_getD_ge bs (2 * j + 1) j (by omega)]
      exact encodeD_data_eq bs j hj
    rw [show 4 * (j + 1) = 4 * j + 4 from by ring, run_add, ih hj', run_four_data heq,
      clearedD_getD_ge bs (2 * j) j (le_refl _)]
    simp only [storedC, clearedD, Nat.mul_succ]

/-- **Self-termination at the detectable boundary.**  On `encodeD bs` the machine clears all `bs.length` data
pairs and halts (`phase 4`) at the terminating marker, position `2·|bs|+1`. -/
theorem clear_halt (bs : List Bool) :
    run clearMachine (4 * bs.length + 2) (init clearMachine (encodeD bs))
      = ⟨(4, false), 2 * bs.length + 1, clearedD bs bs.length⟩ := by
  have hlo : (clearedD bs bs.length).getD (2 * bs.length) false = false := by
    rw [clearedD_getD_ge bs (2 * bs.length) bs.length (le_refl _)]; exact encodeD_mark_lo bs
  have hhi : (clearedD bs bs.length).getD (2 * bs.length + 1) false = true := by
    rw [clearedD_getD_ge bs (2 * bs.length + 1) bs.length (by omega)]; exact encodeD_mark_hi bs
  rw [show 4 * bs.length + 2 = 4 * bs.length + 1 + 1 from by ring, run_succ, run_succ,
    run_clear bs bs.length (le_refl _), step_readLo, hlo,
    step_readHi_marker (by rw [hhi]; simp)]

/-- The clear pass is genuinely halted at the marker. -/
theorem clear_halted (bs : List Bool) :
    clearMachine.halt (run clearMachine (4 * bs.length + 2) (init clearMachine (encodeD bs))).st = true := by
  rw [clear_halt]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinClearMarker

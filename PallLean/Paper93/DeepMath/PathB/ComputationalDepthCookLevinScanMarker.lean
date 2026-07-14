import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinDoubled

/-!
# Cook–Levin M1 — the detectable-termination scan machine

The single-machine weld's run-forever problem: a scan into the `false` padding never stops.  The doubled-encoding
infrastructure (`CookLevinDoubled`) fixes it — a data pair reads *equal* (`00`/`11`), a boundary reads *unequal*
(`01`).  So a machine can scan pairs while the two cells are equal and **halt** the moment they differ.

`scanMachine` does exactly that: `readLo` stores a pair's low cell, `readHi` compares the high cell; equal ⇒
continue, differ ⇒ halt.  `scan_halt`: on `encodeD bs` it halts precisely at the terminating marker — pair
`bs.length` (`firstMarkerD_eq`), position `2·|bs|+1`.  So the scan **self-terminates at the detectable boundary**,
the property the weld needed.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinScanMarker

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled

/-- Control: `State = Fin 3 × Bool` — phase `0`=read-low, `1`=read-high, `2`=halted; paired with the stored low
cell (to compare against the high cell). -/
def scanMachine : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 2)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then (if b = s.2 then ((0, s.2), none, 1) else ((2, s.2), none, 2))
    else ((2, s.2), none, 2)
  accept := fun s => s.2

/-- Read the low cell of a pair, store it, advance. -/
theorem step_readLo {s : Bool} {p : ℕ} {tape : List Bool} :
    step scanMachine ⟨(0, s), p, tape⟩ = ⟨(1, tape.getD p false), p + 1, tape⟩ := by
  simp only [step, scanMachine, moveHead]; rfl

/-- Read the high cell; it equals the stored low cell (data pair) ⇒ continue. -/
theorem step_readHi_eq {s : Bool} {p : ℕ} {tape : List Bool} (h : tape.getD p false = s) :
    step scanMachine ⟨(1, s), p, tape⟩ = ⟨(0, s), p + 1, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, scanMachine, moveHead, h]

/-- Read the high cell; it differs from the stored low cell (marker) ⇒ halt. -/
theorem step_readHi_ne {s : Bool} {p : ℕ} {tape : List Bool} (h : tape.getD p false ≠ s) :
    step scanMachine ⟨(1, s), p, tape⟩ = ⟨(2, s), p, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, scanMachine, moveHead, h]

/-! ## The scan invariant and self-halt at the marker -/

/-- The stored low cell after `j` pairs (irrelevant to termination; tracked for a clean invariant). -/
def storedAt (bs : List Bool) : ℕ → Bool
  | 0 => false
  | j + 1 => (encodeD bs).getD (2 * j) false

/-- Two steps over a data pair (equal cells): advance one pair, staying in the read-low phase. -/
theorem run_two_data {s : Bool} {j : ℕ} {tape : List Bool}
    (heq : tape.getD (2 * j) false = tape.getD (2 * j + 1) false) :
    run scanMachine 2 ⟨(0, s), 2 * j, tape⟩ = ⟨(0, tape.getD (2 * j) false), 2 * j + 2, tape⟩ := by
  rw [run_succ, run_succ, run_zero, step_readLo, step_readHi_eq heq.symm]

/-- **Scan invariant.**  Over the equal-celled data pairs, after `2j` steps the machine is reading a low cell at
position `2j`. -/
theorem run_scan (bs : List Bool) (j : ℕ) (hj : j ≤ bs.length) :
    run scanMachine (2 * j) (init scanMachine (encodeD bs))
      = ⟨(0, storedAt bs j), 2 * j, encodeD bs⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j ≤ bs.length := Nat.le_of_succ_le hj
    have heq : (encodeD bs).getD (2 * j) false = (encodeD bs).getD (2 * j + 1) false :=
      encodeD_data_eq bs j hj
    rw [show 2 * (j + 1) = 2 * j + 2 from by ring, run_add, ih hj', run_two_data heq]
    simp only [storedAt]

/-- **Self-termination at the detectable boundary.**  On `encodeD bs`, the scan halts (`phase 2`) precisely at the
terminating marker — pair `bs.length`, position `2·|bs|+1`. -/
theorem scan_halt (bs : List Bool) :
    run scanMachine (2 * bs.length + 2) (init scanMachine (encodeD bs))
      = ⟨(2, false), 2 * bs.length + 1, encodeD bs⟩ := by
  have hlo : (encodeD bs).getD (2 * bs.length) false = false := encodeD_mark_lo bs
  have hhi : (encodeD bs).getD (2 * bs.length + 1) false = true := encodeD_mark_hi bs
  rw [show 2 * bs.length + 2 = 2 * bs.length + 1 + 1 from by ring, run_succ, run_succ,
    run_scan bs bs.length (le_refl _), step_readLo,
    step_readHi_ne (by rw [hhi, hlo]; simp)]
  rw [hlo]

/-- The scan is genuinely halted at the marker. -/
theorem scan_halted (bs : List Bool) :
    scanMachine.halt (run scanMachine (2 * bs.length + 2) (init scanMachine (encodeD bs))).st = true := by
  rw [scan_halt]; rfl

/-- The scan's stopping index is exactly the detectable boundary `firstMarkerD bs = bs.length`. -/
theorem scan_stops_at_marker (bs : List Bool) :
    2 * firstMarkerD bs + 1 = 2 * bs.length + 1 := by rw [firstMarkerD_eq]

end PallLean.Paper93.DeepMath.PathB.CookLevinScanMarker

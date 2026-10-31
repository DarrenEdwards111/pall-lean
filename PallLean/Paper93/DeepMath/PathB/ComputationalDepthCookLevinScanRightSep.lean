import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinScanLeftSep

/-!
# Cook–Levin M1 — scan-right to `SEP = 01` (the INIT / re-anchor primitive)

The master machine's seams re-anchor the head at `SEP` between sub-machines, and INIT must reach `SEP` from
position `0` — skipping `LSENT = 10` and the counter `11` (so `ScanMarker`, which stops at the first *any* marker,
would wrongly stop at `LSENT`).  This is the rightward twin of `ScanLeftSep`: walk right reading pairs (low then
high), halt at the first `01` (`low=0, high=1`), skipping `10` and data (`00`/`11`).  Since data and `10` are never
`01`, it stops exactly at `SEP`.  (Rightward, so no `Nat` subtraction — cleaner than the leftward version.)

`run_scan_right` (m-pair invariant) and `run_scan_right_halt` (halt at `SEP`) complete the four scan primitives
(right/left × marker/`SEP`) the master seams use.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Control: `State = Fin 3 × Bool` — phase `0`=read-low, `1`=read-high, `2`=halted; stored low cell. -/
def scanRightSep : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 2)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then (if !s.2 && b then ((2, s.2), none, 2) else ((0, s.2), none, 1))
    else ((2, s.2), none, 2)
  accept := fun s => s.2

/-- READLO: read the low cell into the store, step right. -/
theorem step_readlo {s : Bool} {p : ℕ} {tape : List Bool} :
    step scanRightSep ⟨(0, s), p, tape⟩ = ⟨(1, tape.getD p false), p + 1, tape⟩ := by
  simp only [step, scanRightSep, moveHead]; rfl

/-- READHI (non-`SEP`): the pair is not `01`, continue right. -/
theorem step_readhi_cont {s : Bool} {p : ℕ} {tape : List Bool}
    (h : (!s && tape.getD p false) = false) :
    step scanRightSep ⟨(1, s), p, tape⟩ = ⟨(0, s), p + 1, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, scanRightSep, moveHead, h]

/-- READHI (`SEP = 01`): `low = 0, high = 1`, halt. -/
theorem step_readhi_halt {s : Bool} {p : ℕ} {tape : List Bool}
    (h : (!s && tape.getD p false) = true) :
    step scanRightSep ⟨(1, s), p, tape⟩ = ⟨(2, s), p, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, scanRightSep, moveHead, h]

/-- **One non-`SEP` pair in two steps** (head `p → p+2`). -/
theorem run_two_right {s : Bool} {p : ℕ} {tape : List Bool}
    (h : (!(tape.getD p false) && tape.getD (p + 1) false) = false) :
    run scanRightSep 2 ⟨(0, s), p, tape⟩ = ⟨(0, tape.getD p false), p + 2, tape⟩ := by
  rw [run_succ, run_succ, run_zero, step_readlo, step_readhi_cont h]

/-- The stored low cell after scanning `m` pairs. -/
def storedR (tape : List Bool) (P : ℕ) (s : Bool) : ℕ → Bool
  | 0 => s
  | m + 1 => tape.getD (P + 2 * m) false

/-- **Scan-right invariant.**  While the first `m` pairs are non-`SEP`, after `2m` steps the head is at `P + 2m`. -/
theorem run_scan_right (tape : List Bool) (P : ℕ) (s : Bool) (m : ℕ)
    (hns : ∀ i < m, (!(tape.getD (P + 2 * i) false) && tape.getD (P + 2 * i + 1) false) = false) :
    run scanRightSep (2 * m) ⟨(0, s), P, tape⟩ = ⟨(0, storedR tape P s m), P + 2 * m, tape⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hns' : ∀ i < m, (!(tape.getD (P + 2 * i) false) && tape.getD (P + 2 * i + 1) false) = false :=
      fun i hi => hns i (Nat.lt_succ_of_lt hi)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih hns',
      run_two_right (hns m (Nat.lt_succ_self m))]
    simp only [storedR, Nat.mul_succ, Nat.add_assoc]

/-- **Halt at `SEP`.**  If the first `m` pairs are non-`SEP` and pair `m` is `SEP = 01`, then after `2m+2` steps the
machine has halted at the `SEP` high cell `P + 2m + 1`. -/
theorem run_scan_right_halt (tape : List Bool) (P : ℕ) (s : Bool) (m : ℕ)
    (hns : ∀ i < m, (!(tape.getD (P + 2 * i) false) && tape.getD (P + 2 * i + 1) false) = false)
    (hsep : (!(tape.getD (P + 2 * m) false) && tape.getD (P + 2 * m + 1) false) = true) :
    run scanRightSep (2 * m + 2) ⟨(0, s), P, tape⟩
      = ⟨(2, tape.getD (P + 2 * m) false), P + 2 * m + 1, tape⟩ := by
  rw [run_add, run_scan_right tape P s m hns, run_succ, run_succ, run_zero, step_readlo,
    step_readhi_halt hsep]

/-- The scan-right is genuinely halted at `SEP`. -/
theorem scan_right_halted (tape : List Bool) (P : ℕ) (s : Bool) (m : ℕ)
    (hns : ∀ i < m, (!(tape.getD (P + 2 * i) false) && tape.getD (P + 2 * i + 1) false) = false)
    (hsep : (!(tape.getD (P + 2 * m) false) && tape.getD (P + 2 * m + 1) false) = true) :
    scanRightSep.halt (run scanRightSep (2 * m + 2) ⟨(0, s), P, tape⟩).st = true := by
  rw [run_scan_right_halt tape P s m hns hsep]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinDoubled

/-!
# Cook–Levin M1, S6 — scan-left to `SEP = 01` (with a design refinement)

**Refinement of `WELD_PLAN_READAV.md` §1/§3.**  The plan used a *composite* `LSENT = 10 10` and a walk-left with
2-pair lookahead, so the loop could return to a left sentinel.  Re-checking the loop shows that is unnecessary if
the loop is **anchored at `SEP`**: each round checks the pair immediately left of `SEP` (`11` ⇒ counter present,
`10` ⇒ done) and deletes the pairs flanking `SEP`.  Deleting the *rightmost* counter cell decrements the unary
counter exactly as deleting the leading one (`readAv_spec`'s net per-round transform is identical), so this is
correct.  Consequences:
- `LSENT` can be a **single** `10` (checked locally at the loop control), not a composite — simpler encoding.
- The only leftward machine needed is a **scan-left to `SEP = 01`** (single pattern) to reposition from `REND`
  back to `SEP` after a round — no 2-pair lookahead.

This file builds that scan-left: walk left reading pairs (high cell then low cell), halt at the first `01`
(`low = 0, high = 1`), skipping `10` (`REND`) and data (`00`/`11`).  Since data pairs and `REND` are never `01`,
it stops exactly at `SEP`.

Here: the machine, its step lemmas, and `run_two_left_cont` — one non-`SEP` pair traversed in two steps
(head `p → p-2`).  The `m`-pair invariant and the halt-at-`SEP` lemma are the next chunk (mirroring S5).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinScanLeftSep

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Control: `State = Fin 3 × Bool` — phase `0`=read-high, `1`=read-low, `2`=halted; paired with the stored high
cell (to test the pair against `SEP = 01`). -/
def scanLeftSep : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 2)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 0)
    else if s.1 = 1 then (if !b && s.2 then ((2, s.2), none, 2) else ((0, s.2), none, 0))
    else ((2, s.2), none, 2)
  accept := fun s => s.2

/-- READHI: read the high cell into the store, step left. -/
theorem step_readhi {s : Bool} {p : ℕ} {tape : List Bool} :
    step scanLeftSep ⟨(0, s), p, tape⟩ = ⟨(1, tape.getD p false), p - 1, tape⟩ := by
  simp only [step, scanLeftSep, moveHead]; rfl

/-- READLO (non-`SEP`): the pair is not `01`, continue left. -/
theorem step_readlo_cont {s : Bool} {p : ℕ} {tape : List Bool}
    (h : (!(tape.getD p false) && s) = false) :
    step scanLeftSep ⟨(1, s), p, tape⟩ = ⟨(0, s), p - 1, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, scanLeftSep, moveHead, h]

/-- READLO (`SEP = 01`): `low = 0, high = 1`, halt. -/
theorem step_readlo_halt {s : Bool} {p : ℕ} {tape : List Bool}
    (h : (!(tape.getD p false) && s) = true) :
    step scanLeftSep ⟨(1, s), p, tape⟩ = ⟨(2, s), p, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, scanLeftSep, moveHead, h]

/-- **One non-`SEP` pair in two steps.**  The pair `[p-1, p]` (high at `p`, low at `p-1`) is not `01`, so the head
moves left by one pair (`p → p-2`), storing the high cell. -/
theorem run_two_left_cont {s : Bool} {p : ℕ} {tape : List Bool}
    (h : (!(tape.getD (p - 1) false) && tape.getD p false) = false) :
    run scanLeftSep 2 ⟨(0, s), p, tape⟩ = ⟨(0, tape.getD p false), p - 2, tape⟩ := by
  rw [run_succ, run_succ, run_zero, step_readhi, step_readlo_cont h, Nat.sub_sub]

/-! ## The m-pair invariant and the halt at `SEP` -/

/-- The stored high cell after scanning `m` pairs (irrelevant to termination; tracked for a clean invariant). -/
def storedL (tape : List Bool) (P : ℕ) (s : Bool) : ℕ → Bool
  | 0 => s
  | m + 1 => tape.getD (P - 2 * m) false

/-- **Scan-left invariant.**  While the first `m` pairs (going left from `P`) are non-`SEP`, after `2m` steps the
head has moved left by one pair each, to `P - 2m`, still reading a high cell. -/
theorem run_scan_left (tape : List Bool) (P : ℕ) (s : Bool) (m : ℕ)
    (hns : ∀ i < m, (!(tape.getD (P - 2 * i - 1) false) && tape.getD (P - 2 * i) false) = false) :
    run scanLeftSep (2 * m) ⟨(0, s), P, tape⟩ = ⟨(0, storedL tape P s m), P - 2 * m, tape⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hns' : ∀ i < m, (!(tape.getD (P - 2 * i - 1) false) && tape.getD (P - 2 * i) false) = false :=
      fun i hi => hns i (Nat.lt_succ_of_lt hi)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih hns',
      run_two_left_cont (hns m (Nat.lt_succ_self m))]
    simp only [storedL, Nat.sub_sub, Nat.mul_succ]

/-- **Halt at `SEP`.**  If the first `m` pairs are non-`SEP` and pair `m` is `SEP = 01`, then after `2m+2` steps the
machine has halted (`phase 2`) at the `SEP` low cell `P - 2m - 1`. -/
theorem run_scan_left_halt (tape : List Bool) (P : ℕ) (s : Bool) (m : ℕ)
    (hns : ∀ i < m, (!(tape.getD (P - 2 * i - 1) false) && tape.getD (P - 2 * i) false) = false)
    (hsep : (!(tape.getD (P - 2 * m - 1) false) && tape.getD (P - 2 * m) false) = true) :
    run scanLeftSep (2 * m + 2) ⟨(0, s), P, tape⟩
      = ⟨(2, tape.getD (P - 2 * m) false), P - 2 * m - 1, tape⟩ := by
  rw [run_add, run_scan_left tape P s m hns, run_succ, run_succ, run_zero, step_readhi,
    step_readlo_halt hsep]

/-- The scan-left is genuinely halted at `SEP`. -/
theorem scan_left_halted (tape : List Bool) (P : ℕ) (s : Bool) (m : ℕ)
    (hns : ∀ i < m, (!(tape.getD (P - 2 * i - 1) false) && tape.getD (P - 2 * i) false) = false)
    (hsep : (!(tape.getD (P - 2 * m - 1) false) && tape.getD (P - 2 * m) false) = true) :
    scanLeftSep.halt (run scanLeftSep (2 * m + 2) ⟨(0, s), P, tape⟩).st = true := by
  rw [run_scan_left_halt tape P s m hns hsep]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinScanLeftSep

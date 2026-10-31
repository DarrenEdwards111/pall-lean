import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinScanLeftSep

/-!
# Cook–Levin M1, S7 + S8 — the loop-control and read-result end-machines

With the SEP-anchored loop (see `CookLevinScanLeftSep`), the loop head sits at the `SEP` **low** cell.  Two small
machines close the loop:

* **S7 `loopCtrl`** — the counter-empty test.  Read the *high* cell of the pair immediately left of `SEP`: it is
  `1` for a counter pair (`11`, low=high=1 ⇒ round) and `0` for `LSENT` (`10`, low=1,high=0 ⇒ done).  Two steps
  (step left, read), halting with `accept` = that bit.
* **S8 `readRes`** — once the counter is empty, `a_v` is the pair right of `SEP`; read its low cell (`SEP+2`).
  Three steps (right, right, read), halting with `accept = a_v`.

Both are run-lemmas (components) that self-halt.  They complete the sub-machine inventory (S1–S8); what remains is
the master machine (tagged union of the δ's with control-only seams) and the correctness chain to `readAv_spec`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinLoopEnds

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-! ## S7 — loop control -/

/-- Control: `State = Fin 3 × Bool` — phase `0`=step-left, `1`=read, `2`=halted; stored result bit. -/
def loopCtrl : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 2)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2), none, 0)
    else if s.1 = 1 then ((2, b), none, 2)
    else ((2, s.2), none, 2)
  accept := fun s => s.2

theorem loopCtrl_step_left {s : Bool} {q : ℕ} {tape : List Bool} :
    step loopCtrl ⟨(0, s), q, tape⟩ = ⟨(1, s), q - 1, tape⟩ := by
  simp only [step, loopCtrl, moveHead]; rfl

theorem loopCtrl_step_read {s : Bool} {p : ℕ} {tape : List Bool} :
    step loopCtrl ⟨(1, s), p, tape⟩ = ⟨(2, tape.getD p false), p, tape⟩ := by
  simp only [step, loopCtrl, moveHead]; rfl

/-- **S7 result.**  From the `SEP` low cell `q`, two steps read the high cell of the pair left of `SEP` (`q-1`)
into `accept` and halt: `1` ⇒ counter present (round), `0` ⇒ `LSENT` (done). -/
theorem run_loopCtrl {s : Bool} {q : ℕ} {tape : List Bool} :
    run loopCtrl 2 ⟨(0, s), q, tape⟩ = ⟨(2, tape.getD (q - 1) false), q - 1, tape⟩ := by
  rw [run_succ, run_succ, run_zero, loopCtrl_step_left, loopCtrl_step_read]

theorem loopCtrl_halted {s : Bool} {q : ℕ} {tape : List Bool} :
    loopCtrl.halt (run loopCtrl 2 ⟨(0, s), q, tape⟩).st = true := by
  rw [run_loopCtrl]; rfl

/-! ## S8 — read result -/

/-- Control: `State = Fin 4 × Bool` — phases `0,1`=step-right, `2`=read, `3`=halted; stored `a_v`. -/
def readRes : Machine where
  State := Fin 4 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 3)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2), none, 1)
    else if s.1 = 1 then ((2, s.2), none, 1)
    else if s.1 = 2 then ((3, b), none, 2)
    else ((3, s.2), none, 2)
  accept := fun s => s.2

theorem readRes_step0 {s : Bool} {q : ℕ} {tape : List Bool} :
    step readRes ⟨(0, s), q, tape⟩ = ⟨(1, s), q + 1, tape⟩ := by
  simp only [step, readRes, moveHead]; rfl

theorem readRes_step1 {s : Bool} {q : ℕ} {tape : List Bool} :
    step readRes ⟨(1, s), q, tape⟩ = ⟨(2, s), q + 1, tape⟩ := by
  simp only [step, readRes, moveHead]; rfl

theorem readRes_step_read {s : Bool} {p : ℕ} {tape : List Bool} :
    step readRes ⟨(2, s), p, tape⟩ = ⟨(3, tape.getD p false), p, tape⟩ := by
  simp only [step, readRes, moveHead]; rfl

/-- **S8 result.**  From the `SEP` low cell `q`, three steps read the low cell of the pair right of `SEP`
(`q+2 = a_v`) into `accept` and halt. -/
theorem run_readRes {s : Bool} {q : ℕ} {tape : List Bool} :
    run readRes 3 ⟨(0, s), q, tape⟩ = ⟨(3, tape.getD (q + 2) false), q + 2, tape⟩ := by
  rw [run_succ, run_succ, run_succ, run_zero, readRes_step0, readRes_step1, readRes_step_read]

theorem readRes_halted {s : Bool} {q : ℕ} {tape : List Bool} :
    readRes.halt (run readRes 3 ⟨(0, s), q, tape⟩).st = true := by
  rw [run_readRes]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinLoopEnds

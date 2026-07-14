import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEvalMachine

/-!
# Cook–Levin M1 — a COMPLETE single halting machine for indexed read (interleaved encoding)

**Honest framing.**  The genuine separate-region `read a_v` needs the two-pointer, and welding it into one *halting*
Boolean-tape machine needs a detectable end-marker — which on a two-symbol tape means a *doubled* encoding, doubling
every phase.  That full weld is a major construction (500–1000+ lines) not delivered here.

What *is* delivered is a **complete single halting machine** that reads a unary-indexed value when the index and
data are **interleaved** — `1 a_0 1 a_1 … 1 a_{v-1} 0 a_v`.  It scans `(flag, value)` pairs; while the flag is
`true` it skips the value; at the first `false` flag it grabs that pair's value (`a_v`) and halts.  This is the
`read a_v` machine *structure*, complete: `readIdx ∈ ComposableMachine.InP` (`readInterleaved_inP`).

**Scope line (do not overstate).**  This requires interleaved input.  The SAT verifier's assignment is a *free
witness in a separate region*, which cannot be pre-interleaved with the formula's variable references — so the
genuine SAT lookup still needs the separate-region two-pointer weld (`DeleteShift.run_shift` + `ReadAv.readAv_spec`
give its inner shift and its algorithm; the halting single-machine assembly remains).  This file is the interleaved
case only.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinReadInterleaved

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEvalMachine (getD_pad flagFalse_exists firstFalseFlag)

/-- Control: `State = Fin 4 × Bool` — phase `0`=read-flag, `1`=skip-value, `2`=grab-value, `3`=halted; paired
with the grabbed output bit. -/
def readMachine : Machine where
  State := Fin 4 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 3)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((2, s.2), none, 1))
    else if s.1 = 1 then ((0, s.2), none, 1)
    else if s.1 = 2 then ((3, b), none, 2)
    else ((3, s.2), none, 2)
  accept := fun s => s.2

/-- The decided value: the value of the pair at the first `false` flag (the `v`-th pair). -/
def readIdx (x : List Bool) : Bool := x.getD (2 * firstFalseFlag x + 1) false

/-- Read a `true` flag → skip this pair's value. -/
theorem step_flag_true {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step readMachine ⟨(0, s), p, x⟩ = ⟨(1, s), p + 1, x⟩ := by
  simp only [step, readMachine, h, moveHead]; rfl

/-- Read a `false` flag → this is the target pair; go grab its value. -/
theorem step_flag_false {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step readMachine ⟨(0, s), p, x⟩ = ⟨(2, s), p + 1, x⟩ := by
  simp only [step, readMachine, h, moveHead]; rfl

/-- Skip a value, back to reading a flag. -/
theorem step_skip {s : Bool} {p : ℕ} {x : List Bool} :
    step readMachine ⟨(1, s), p, x⟩ = ⟨(0, s), p + 1, x⟩ := by
  simp only [step, readMachine, moveHead]; rfl

/-- Grab the target value and halt (storing it as the output). -/
theorem step_grab {s : Bool} {p : ℕ} {x : List Bool} :
    step readMachine ⟨(2, s), p, x⟩ = ⟨(3, x.getD p false), p, x⟩ := by
  simp only [step, readMachine, moveHead]; rfl

/-- **Scan invariant.**  While the flags are `true`, after `2j` steps the machine is reading a flag at position
`2j` with no value grabbed yet. -/
theorem run_two_j (x : List Bool) (j : ℕ) (hj : ∀ i < j, x.getD (2 * i) false = true) :
    run readMachine (2 * j) (init readMachine x) = ⟨(0, false), 2 * j, x⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : ∀ i < j, x.getD (2 * i) false = true := fun i hi => hj i (Nat.lt_succ_of_lt hi)
    have hflag : x.getD (2 * j) false = true := hj j (Nat.lt_succ_self j)
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e1, run_succ, run_succ, ih hj', step_flag_true hflag, step_skip]

/-- **Halt.**  At the first `false` flag (`J`), the machine grabs `a_v = x.getD (2J+1)` and halts. -/
theorem run_halt (x : List Bool) :
    run readMachine (2 * firstFalseFlag x + 2) (init readMachine x)
      = ⟨(3, x.getD (2 * firstFalseFlag x + 1) false), 2 * firstFalseFlag x + 1, x⟩ := by
  have hff : x.getD (2 * firstFalseFlag x) false = false := Nat.find_spec (flagFalse_exists x)
  have hmin : ∀ i < firstFalseFlag x, x.getD (2 * i) false = true :=
    fun i hi => by simpa using Nat.find_min (flagFalse_exists x) hi
  rw [show 2 * firstFalseFlag x + 2 = 2 * firstFalseFlag x + 1 + 1 from by ring,
    run_succ, run_succ, run_two_j x (firstFalseFlag x) hmin, step_flag_false hff, step_grab]

/-- **The machine decides `readIdx` in poly time.** -/
theorem readInterleaved_decides : Decides readMachine readIdx (fun n => 2 * n + 2) := by
  intro x
  have hJle : firstFalseFlag x ≤ x.length := Nat.find_le (getD_pad x (by omega))
  have hhalt := run_halt x
  have hst : readMachine.halt (run readMachine (2 * firstFalseFlag x + 2) (init readMachine x)).st = true := by
    rw [hhalt]; rfl
  have hle : 2 * firstFalseFlag x + 2 ≤ 2 * x.length + 2 := by omega
  have hstable : run readMachine (2 * x.length + 2) (init readMachine x)
      = run readMachine (2 * firstFalseFlag x + 2) (init readMachine x) :=
    run_stable readMachine x hle hst
  refine ⟨?_, ?_⟩
  · show readMachine.halt (run readMachine (2 * x.length + 2) (init readMachine x)).st = true
    rw [hstable]; exact hst
  · show readMachine.accept (run readMachine (2 * x.length + 2) (init readMachine x)).st = readIdx x
    rw [hstable, hhalt]; rfl

/-- **A complete single halting machine for interleaved indexed read, in the faithful `ComposableMachine.InP`.** -/
theorem readInterleaved_inP : InP readIdx :=
  ⟨readMachine, fun n => 2 * n + 2, ⟨2, 1, fun n => by simp only [pow_one]; omega⟩, readInterleaved_decides⟩

end PallLean.Paper93.DeepMath.PathB.CookLevinReadInterleaved

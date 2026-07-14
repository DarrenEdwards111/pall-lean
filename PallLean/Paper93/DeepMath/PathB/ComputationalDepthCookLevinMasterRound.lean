import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinMasterSim

/-!
# Cook–Levin M1 — the seam-step glue (composing the group sims across seams)

The group simulation lemmas (`CookLevinMasterSim`) lift each sub-machine's run up to its halt sub-phase.  Between
two groups the master takes a **control-only seam**: one master step at the halted sub-phase that re-tags the group,
resets the sub-phase, and moves the head by a fixed amount (never writing).  This file proves those seam steps —
the connective tissue that stitches consecutive group runs into one round.

The head-move on each seam was re-derived from the doubled-tape geometry (see `CookLevinMaster`): a round starts with
the head at the `SEP` low cell `s`, and the corrected seams route

  `INIT`(s+1)─(−1)→`LOOPCHK`(s)  →  read counter → `REPA`(+1,+1)→`SHA`(s+2, delete a₀) → `RANCH1`(stay, high cell)
  → scan to `SEP`(s) →(−1)`REPB`(−1)→`SHB`(s−2, delete counter) → `RANCH2`(stay) → scan to new `SEP`(s−2)
  →(stay, loop) `LOOPCHK`,

and on the empty-counter branch `LOOPCHK`(s)→(+1)`RRES`(s, read a_v at s+2)→(stay)`HALT` (carrying `a_v = c₀`).

Each lemma is local (one `step` at a concrete `(group, sub-phase)`), proved by reducing `masterM`'s δ at that state.
These are exactly the seams the per-round composition (next chunk) inserts between the `sim_run_*` lifts.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinLoopEnds

/-- One step as a one-step run (peels a seam out of a `run_add` decomposition). -/
theorem run_one (M : Machine) (c : Cfg M) : run M 1 c = step M c := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero]

/-! ## Seam steps between groups -/

/-- `INIT → LOOPCHK`: at the `SEP` high cell, step left to the `SEP` low cell. -/
theorem seam_INIT {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(0, 2, c0, c1), p, tape⟩ = ⟨(1, 0, false, false), p - 1, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- `LOOPCHK → REPA` (counter present, `c₀ = true`): step right toward `a₀`. -/
theorem seam_LOOPCHK_true {c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(1, 2, true, c1), p, tape⟩ = ⟨(2, 0, false, false), p + 1, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- `LOOPCHK → RRES` (counter empty, `c₀ = false`): step right to the `SEP` low cell. -/
theorem seam_LOOPCHK_false {c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(1, 2, false, c1), p, tape⟩ = ⟨(8, 0, false, false), p + 1, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- **REPA reposition** (`SEP` low `p` → `a₀` low `p+2`): two internal steps, then the group is `SHA`. -/
theorem repa_run {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    run masterM 2 ⟨(2, 0, c0, c1), p, tape⟩ = ⟨(3, 0, false, false), p + 2, tape⟩ := by
  rw [run_succ, run_succ, run_zero]
  simp only [step, masterM, seam, moveHead,
    show masterM.halt ((2 : Fin 10), (0 : Fin 9), c0, c1) = false from rfl]
  norm_num
  simp [step, masterM, seam, moveHead]

/-- `SHA → RANCH1`: `SHA` halts on a high cell (the newly-written `REND` high) = `RANCH1`'s start ⇒ stay. -/
theorem seam_SHA {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(3, 8, c0, c1), p, tape⟩ = ⟨(4, 0, false, false), p, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- `RANCH1 → REPB`: at the `SEP` low cell, step left toward the counter. -/
theorem seam_RANCH1 {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(4, 2, c0, c1), p, tape⟩ = ⟨(5, 0, false, false), p - 1, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- **REPB reposition** (one seam step, `−1`): `→ SHB` at the counter low cell. -/
theorem repb_step {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(5, 0, c0, c1), p, tape⟩ = ⟨(6, 0, false, false), p - 1, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- `SHB → RANCH2`: `SHB` halts on a high cell = `RANCH2`'s start ⇒ stay. -/
theorem seam_SHB {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(6, 8, c0, c1), p, tape⟩ = ⟨(7, 0, false, false), p, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- `RANCH2 → LOOPCHK` (loop back): at the new `SEP` low cell ⇒ stay; next round starts here. -/
theorem seam_RANCH2 {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(7, 2, c0, c1), p, tape⟩ = ⟨(1, 0, false, false), p, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-- `RRES → HALT`: carry `a_v` (`= c₀`) into the `HALT` group so `accept` reads it; stay. -/
theorem seam_RRES {c0 c1 : Bool} {p : ℕ} {tape : List Bool} :
    step masterM ⟨(8, 3, c0, c1), p, tape⟩ = ⟨(9, 0, c0, c1), p, tape⟩ := by
  simp [step, masterM, seam, moveHead]

/-! ## The termination path (empty counter): compose LOOPCHK + RRES across their seams

This is the first genuine per-segment composition: it stitches two group sims (`sim_run_LOOPCHK`, `sim_run_RRES`)
through the intervening seams (`seam_LOOPCHK_false`, `seam_RRES`) into one master run.  Both sub-machines run a
*fixed* number of steps (2 and 3), so their `hmin` "off the halt phase" hypotheses are geometry-free (proved by
`interval_cases`).  Starting at the loop head (`SEP` low `s`) with an empty counter (the cell left of `SEP` is `0`),
the master reads `a_v` at `s+2` and halts in the `HALT` group carrying `a_v` in `c₀`. -/
theorem tail_read {s : ℕ} {tape : List Bool} (hs : 1 ≤ s)
    (hdone : tape.getD (s - 1) false = false) :
    run masterM 7 ⟨(1, 0, false, false), s, tape⟩
      = ⟨(9, 0, tape.getD (s + 2) false, false), s + 2, tape⟩ := by
  have hsq : s - 1 + 1 = s := Nat.sub_add_cancel hs
  have hmin1 : ∀ i < 2, (run loopCtrl i ⟨(0, false), s, tape⟩).st.1 ≠ 2 := by
    intro i hi; interval_cases i
    · simp
    · rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, loopCtrl_step_left]; simp
  have hmin2 : ∀ i < 3, (run readRes i ⟨(0, false), s, tape⟩).st.1 ≠ 3 := by
    intro i hi; interval_cases i
    · simp
    · rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, readRes_step0]; simp
    · rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero,
        readRes_step0, readRes_step1]; simp
  -- LOOPCHK group sim (2 steps) → reads the empty-counter bit into c₀
  have e1 : run masterM 2 ⟨(1, 0, false, false), s, tape⟩ = ⟨(1, 2, false, false), s - 1, tape⟩ := by
    rw [show (⟨(1, 0, false, false), s, tape⟩ : Cfg masterM) = embedLoop 1 ⟨(0, false), s, tape⟩ from rfl,
      sim_run_LOOPCHK 2 ⟨(0, false), s, tape⟩ hmin1, run_loopCtrl, hdone]
    rfl
  -- seam LOOPCHK → RRES (empty counter): step right to the SEP low cell
  have e2 : step masterM ⟨(1, 2, false, false), s - 1, tape⟩ = ⟨(8, 0, false, false), s, tape⟩ := by
    rw [seam_LOOPCHK_false, hsq]
  -- RRES group sim (3 steps) → reads a_v at s+2 into c₀
  have e3 : run masterM 3 ⟨(8, 0, false, false), s, tape⟩
      = ⟨(8, 3, tape.getD (s + 2) false, false), s + 2, tape⟩ := by
    rw [show (⟨(8, 0, false, false), s, tape⟩ : Cfg masterM) = embedRes 8 ⟨(0, false), s, tape⟩ from rfl,
      sim_run_RRES 3 ⟨(0, false), s, tape⟩ hmin2, run_readRes]
    rfl
  -- seam RRES → HALT: carry a_v (= c₀) into the accept
  have e4 : step masterM ⟨(8, 3, tape.getD (s + 2) false, false), s + 2, tape⟩
      = ⟨(9, 0, tape.getD (s + 2) false, false), s + 2, tape⟩ := seam_RRES
  -- assemble nested (each `run_add` exposes exactly one seam `run 1`, so `run_one` is unambiguous)
  have step1 : run masterM (2 + 1) ⟨(1, 0, false, false), s, tape⟩ = ⟨(8, 0, false, false), s, tape⟩ := by
    rw [run_add, e1, run_one, e2]
  have step2 : run masterM (2 + 1 + 3) ⟨(1, 0, false, false), s, tape⟩
      = ⟨(8, 3, tape.getD (s + 2) false, false), s + 2, tape⟩ := by
    rw [run_add, step1, e3]
  have step3 : run masterM (2 + 1 + 3 + 1) ⟨(1, 0, false, false), s, tape⟩
      = ⟨(9, 0, tape.getD (s + 2) false, false), s + 2, tape⟩ := by
    rw [run_add, step2, run_one, e4]
  rw [show (7 : ℕ) = 2 + 1 + 3 + 1 from rfl, step3]

/-- The termination path genuinely halts with `accept = a_v`. -/
theorem tail_read_halts {s : ℕ} {tape : List Bool} (hs : 1 ≤ s)
    (hdone : tape.getD (s - 1) false = false) :
    masterM.halt (run masterM 7 ⟨(1, 0, false, false), s, tape⟩).st = true
      ∧ masterM.accept (run masterM 7 ⟨(1, 0, false, false), s, tape⟩).st = tape.getD (s + 2) false := by
  rw [tail_read hs hdone]
  exact ⟨rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound

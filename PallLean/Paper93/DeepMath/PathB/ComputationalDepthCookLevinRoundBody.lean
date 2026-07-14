import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinMasterRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinPhaseBounds

/-!
# Cook–Levin M1 — the counter-present round body (composition, first half)

The counter-present branch of the loop is `LOOPCHK → REPA → SHA → RANCH1 → REPB → SHB → RANCH2 → (loop)`.  This
file composes its opening half — `LOOPCHK → REPA → SHA` — into one master run, the counter-present analogue of
`tail_read`.  The new ingredient over `tail_read` is that `SHA` (a `rendShift` delete of `a₀`) runs a
*tape-dependent* number of steps `8K+8`, so its `sim_run` `hmin` is discharged by `rendShift_no_early_halt`
(CookLevinPhaseBounds) from the doubled-tape non-`REND` hypotheses.

`round_open`: from the loop head at the `SEP` low cell `s` with the counter present (`T[s-1] = 1`) and the data
right of `SEP` a run of `K` non-`REND` pairs terminated by `REND`, the master reads the counter, repositions to
`a₀`, deletes it (shifting the data left by one pair and re-writing `REND`), and lands at the `RANCH1` entry on a
high cell with the `a₀`-deleted tape `rsTape T (s+2) (K+1)`.

The second half (`RANCH1 → REPB → SHB → RANCH2 → loop`, using `scanLeftSep_no_early_halt` and a second `rendShift`
delete on the evolved tape) composes the same way and closes the loop back to `LOOPCHK`; that plus the whole-run
induction on `v` into `readAv_spec` is the next chunk.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinRoundBody

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinLoopEnds
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds

/-- **Counter-present round body, opening half** (`LOOPCHK → REPA → SHA`).  Reads the counter (present), repositions
to `a₀` low, and deletes the `a₀` pair; lands at `RANCH1`'s entry on a high cell with the `a₀`-deleted tape. -/
theorem round_open {s K : ℕ} {T : List Bool} (hs : 1 ≤ s)
    (hcnt : T.getD (s - 1) false = true)
    (hnr : ∀ i < K, (T.getD (s + 2 + 2 * i + 2) false && !(T.getD (s + 2 + 2 * i + 3) false)) = false)
    (hrend : (T.getD (s + 2 + 2 * K + 2) false && !(T.getD (s + 2 + 2 * K + 3) false)) = true) :
    run masterM (2 + 1 + 2 + (8 * K + 8) + 1) ⟨(1, 0, false, false), s, T⟩
      = ⟨(4, 0, false, false), s + 2 + 2 * K + 1, rsTape T (s + 2) (K + 1)⟩ := by
  have hsq : s - 1 + 1 = s := Nat.sub_add_cancel hs
  -- LOOPCHK's hmin is geometry-free (fixed 2 steps)
  have hmin1 : ∀ i < 2, (run loopCtrl i ⟨(0, false), s, T⟩).st.1 ≠ 2 := by
    intro i hi; interval_cases i
    · simp
    · rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, loopCtrl_step_left]; simp
  -- LOOPCHK group sim: read the counter bit (present)
  have e1 : run masterM 2 ⟨(1, 0, false, false), s, T⟩ = ⟨(1, 2, true, false), s - 1, T⟩ := by
    rw [show (⟨(1, 0, false, false), s, T⟩ : Cfg masterM) = embedLoop 1 ⟨(0, false), s, T⟩ from rfl,
      sim_run_LOOPCHK 2 ⟨(0, false), s, T⟩ hmin1, run_loopCtrl, hcnt]
    rfl
  -- seam LOOPCHK → REPA (counter present): step right
  have e2 : step masterM ⟨(1, 2, true, false), s - 1, T⟩ = ⟨(2, 0, false, false), s, T⟩ := by
    rw [seam_LOOPCHK_true, hsq]
  -- SHA group sim: delete a₀ (tape-dependent 8K+8 steps; hmin from rendShift_no_early_halt)
  have eSHA : run masterM (8 * K + 8) ⟨(3, 0, false, false), s + 2, T⟩
      = ⟨(3, 8, T.getD (s + 2 + 2 * K + 2) false, T.getD (s + 2 + 2 * K + 3) false),
          s + 2 + 2 * K + 1, rsTape T (s + 2) (K + 1)⟩ := by
    rw [show (⟨(3, 0, false, false), s + 2, T⟩ : Cfg masterM) = embedRend 3 ⟨(0, false, false), s + 2, T⟩ from rfl,
      sim_run_SHA (8 * K + 8) ⟨(0, false, false), s + 2, T⟩ (rendShift_no_early_halt hnr),
      run_shift_halt T (s + 2) false false K hnr hrend]
    rfl
  -- assemble nested (each run_add exposes exactly one seam run 1)
  have step1 : run masterM (2 + 1) ⟨(1, 0, false, false), s, T⟩ = ⟨(2, 0, false, false), s, T⟩ := by
    rw [run_add, e1, run_one, e2]
  have step2 : run masterM (2 + 1 + 2) ⟨(1, 0, false, false), s, T⟩ = ⟨(3, 0, false, false), s + 2, T⟩ := by
    rw [run_add, step1, repa_run]
  have step3 : run masterM (2 + 1 + 2 + (8 * K + 8)) ⟨(1, 0, false, false), s, T⟩
      = ⟨(3, 8, T.getD (s + 2 + 2 * K + 2) false, T.getD (s + 2 + 2 * K + 3) false),
          s + 2 + 2 * K + 1, rsTape T (s + 2) (K + 1)⟩ := by
    rw [run_add, step2, eSHA]
  rw [run_add, step3, run_one, seam_SHA]

end PallLean.Paper93.DeepMath.PathB.CookLevinRoundBody

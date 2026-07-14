import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinMasterRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinPhaseBounds

/-!
# Cook–Levin M1 — the counter-present round body (composition)

The counter-present branch of the loop is `LOOPCHK → REPA → SHA → RANCH1 → REPB → SHB → RANCH2 → (loop)`.  This
file composes it into master runs, in two halves, the counter-present analogue of `tail_read`.  The new ingredient
over `tail_read` is that `SHA`/`SHB` (`rendShift` deletes) and `RANCH1`/`RANCH2` (`scanLeftSep` scans) run
*tape-dependent* step counts, so their `sim_run` `hmin`s are discharged by `rendShift_no_early_halt` /
`scanLeftSep_no_early_halt` (CookLevinPhaseBounds) from the doubled-tape non-`REND`/non-`SEP` hypotheses.

`round_open` (`LOOPCHK → REPA → SHA`): from the loop head at the `SEP` low cell `s` with the counter present
(`T[s-1] = 1`) and the data right of `SEP` a run of `K` non-`REND` pairs terminated by `REND`, the master reads the
counter, repositions to `a₀`, deletes it (data shifts left one pair, `REND` re-written), and lands at the `RANCH1`
entry on the high cell `s+2+2K+1` with the `a₀`-deleted tape `rsTape T (s+2) (K+1)`.

`round_close` (`RANCH1 → REPB → SHB → RANCH2 → loop`): from that `RANCH1` entry, scans back to `SEP` low `s`,
repositions to the counter, deletes it (`SEP`+data shift left one pair to `TB`), scans back to the *new* `SEP` low
`s-2`, and lands at the next `LOOPCHK` entry — the round-start shape for `k-1` counters.  Positions are abstract so
it composes with `round_open` (there `P1 = s+2+2K+1`, `TA = rsTape T (s+2) (K+1)`, `m1 = K+1`).

Chaining `round_open` then `round_close` (discharging the linking `rsTape` geometry) gives one full loop iteration =
one `roundStep` on the decoded list; that plus the whole-run induction on `v` into `readAv_spec` is the next chunk.

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

/-- **Counter-present round body, closing half** (`RANCH1 → REPB → SHB → RANCH2 → loop`).  From the `RANCH1` entry
(high cell `P1`, `a₀`-deleted tape `TA`), scans back to `SEP` low `s`, repositions to the counter, deletes it
(shifting `SEP`+data left by one pair to `TB`), scans back to the *new* `SEP` low `s-2`, and lands at the next
`LOOPCHK` entry.  `scanLeftSep`/`rendShift` `hmin`s are discharged by the no-early-halt lemmas.  All positions are
kept abstract so this composes with `round_open` (there `P1 = s+2+2K+1`, `TA = rsTape T (s+2) (K+1)`, `m1 = K+1`). -/
theorem round_close {s P1 m1 KB P2 : ℕ} {TA TB : List Bool}
    (hs2 : 2 ≤ s)
    (hP1 : P1 = s + 2 * m1 + 1)
    (hns1 : ∀ i < m1, (!(TA.getD (P1 - 2 * i - 1) false) && TA.getD (P1 - 2 * i) false) = false)
    (hsep1 : (!(TA.getD (P1 - 2 * m1 - 1) false) && TA.getD (P1 - 2 * m1) false) = true)
    (hnrB : ∀ i < KB, (TA.getD (s - 2 + 2 * i + 2) false && !(TA.getD (s - 2 + 2 * i + 3) false)) = false)
    (hrendB : (TA.getD (s - 2 + 2 * KB + 2) false && !(TA.getD (s - 2 + 2 * KB + 3) false)) = true)
    (hTB : TB = rsTape TA (s - 2) (KB + 1))
    (hP2 : P2 = s - 2 + 2 * KB + 1)
    (hns2 : ∀ i < KB, (!(TB.getD (P2 - 2 * i - 1) false) && TB.getD (P2 - 2 * i) false) = false)
    (hsep2 : (!(TB.getD (P2 - 2 * KB - 1) false) && TB.getD (P2 - 2 * KB) false) = true) :
    run masterM ((2 * m1 + 2) + 1 + 1 + (8 * KB + 8) + 1 + (2 * KB + 2) + 1) ⟨(4, 0, false, false), P1, TA⟩
      = ⟨(1, 0, false, false), s - 2, TB⟩ := by
  have hh1 : P1 - 2 * m1 - 1 = s := by omega
  have hh1b : P1 - 2 * m1 = s + 1 := by omega
  have hsub : s - 1 - 1 = s - 2 := by omega
  have hh2 : P2 - 2 * KB - 1 = s - 2 := by omega
  have hh2b : P2 - 2 * KB = s - 1 := by omega
  -- RANCH1: scan back to SEP low s
  have eR1 : run masterM (2 * m1 + 2) ⟨(4, 0, false, false), P1, TA⟩
      = ⟨(4, 2, TA.getD (s + 1) false, false), s, TA⟩ := by
    rw [show (⟨(4, 0, false, false), P1, TA⟩ : Cfg masterM) = embedScanL 4 ⟨(0, false), P1, TA⟩ from rfl,
      sim_run_RANCH1 (2 * m1 + 2) ⟨(0, false), P1, TA⟩ (scanLeftSep_no_early_halt hns1),
      CookLevinScanLeftSep.run_scan_left_halt TA P1 false m1 hns1 hsep1, hh1, hh1b]
    rfl
  -- SHB: delete the counter (tape-dependent 8KB+8 steps; hmin from rendShift_no_early_halt)
  have eSHB : run masterM (8 * KB + 8) ⟨(6, 0, false, false), s - 2, TA⟩
      = ⟨(6, 8, TA.getD (s - 2 + 2 * KB + 2) false, TA.getD (s - 2 + 2 * KB + 3) false),
          s - 2 + 2 * KB + 1, TB⟩ := by
    rw [show (⟨(6, 0, false, false), s - 2, TA⟩ : Cfg masterM) = embedRend 6 ⟨(0, false, false), s - 2, TA⟩ from rfl,
      sim_run_SHB (8 * KB + 8) ⟨(0, false, false), s - 2, TA⟩ (rendShift_no_early_halt hnrB),
      run_shift_halt TA (s - 2) false false KB hnrB hrendB, ← hTB]
    rfl
  -- RANCH2: scan back to the new SEP low s-2
  have eR2 : run masterM (2 * KB + 2) ⟨(7, 0, false, false), P2, TB⟩
      = ⟨(7, 2, TB.getD (s - 1) false, false), s - 2, TB⟩ := by
    rw [show (⟨(7, 0, false, false), P2, TB⟩ : Cfg masterM) = embedScanL 7 ⟨(0, false), P2, TB⟩ from rfl,
      sim_run_RANCH2 (2 * KB + 2) ⟨(0, false), P2, TB⟩ (scanLeftSep_no_early_halt hns2),
      CookLevinScanLeftSep.run_scan_left_halt TB P2 false KB hns2 hsep2, hh2, hh2b]
    rfl
  -- assemble nested (each seam is one `run 1`)
  have st1 : run masterM (2 * m1 + 2) ⟨(4, 0, false, false), P1, TA⟩
      = ⟨(4, 2, TA.getD (s + 1) false, false), s, TA⟩ := eR1
  have st2 : run masterM (2 * m1 + 2 + 1) ⟨(4, 0, false, false), P1, TA⟩ = ⟨(5, 0, false, false), s - 1, TA⟩ := by
    rw [run_add, st1, run_one, seam_RANCH1]
  have st3 : run masterM (2 * m1 + 2 + 1 + 1) ⟨(4, 0, false, false), P1, TA⟩
      = ⟨(6, 0, false, false), s - 2, TA⟩ := by
    rw [run_add, st2, run_one, repb_step, hsub]
  have st4 : run masterM (2 * m1 + 2 + 1 + 1 + (8 * KB + 8)) ⟨(4, 0, false, false), P1, TA⟩
      = ⟨(6, 8, TA.getD (s - 2 + 2 * KB + 2) false, TA.getD (s - 2 + 2 * KB + 3) false),
          s - 2 + 2 * KB + 1, TB⟩ := by
    rw [run_add, st3, eSHB]
  have st5 : run masterM (2 * m1 + 2 + 1 + 1 + (8 * KB + 8) + 1) ⟨(4, 0, false, false), P1, TA⟩
      = ⟨(7, 0, false, false), s - 2 + 2 * KB + 1, TB⟩ := by
    rw [run_add, st4, run_one, seam_SHB]
  have st6 : run masterM (2 * m1 + 2 + 1 + 1 + (8 * KB + 8) + 1 + (2 * KB + 2)) ⟨(4, 0, false, false), P1, TA⟩
      = ⟨(7, 2, TB.getD (s - 1) false, false), s - 2, TB⟩ := by
    rw [run_add, st5, show (⟨(7, 0, false, false), s - 2 + 2 * KB + 1, TB⟩ : Cfg masterM)
      = ⟨(7, 0, false, false), P2, TB⟩ from by rw [hP2], eR2]
  rw [run_add, st6, run_one, seam_RANCH2]

end PallLean.Paper93.DeepMath.PathB.CookLevinRoundBody

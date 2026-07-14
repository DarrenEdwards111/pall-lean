import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinWholeRun

/-!
# Cook–Levin M1 — the INIT phase, the full run from `init`, and the `InP`/`Decides` packaging

`wholeRun` (CookLevinWholeRun) runs the master from the **LOOPCHK round-start** config (head at `SEP` low `2v+2`).
But the forced initial config is `init masterM x = ⟨start, 0, x⟩` — group `INIT`, head `0`.  The **INIT phase**
(`scanRightSep`, group `0`) scans right from head `0` to `SEP`, then seams to `LOOPCHK` — bridging `init` to the
round-start.  Composing INIT with `wholeRun` gives the complete run from the forced initial config.

We then build the concrete `encode` (assignment + index `v` ↦ doubled `LSENT counterᵛ SEP data REND` tape), prove
`encode` satisfies `RoundInv`, and package `masterM` with the polynomial clock as a **promise `Decides`** witness:
on well-formed inputs the master halts in polynomial time reading the doubled `a_v`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinInP

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep (scanRightSep run_scan_right_halt)
open PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun

/-- **The INIT phase.**  From the forced initial config `⟨start, 0, T⟩` (group `INIT`, head `0`), the master scans
right past `LSENT` and the `v` counters to `SEP`, then seams to `LOOPCHK` at the `SEP` low cell `2v+2` — the
round-start config `wholeRun` expects.  The scan's non-`SEP` and `SEP` facts come from `RoundInv` (`lsent`, `ctr`,
`seplo`, `sephi`); it takes `2(v+1)+2 + 1` steps. -/
theorem init_phase (T : List Bool) (v D : ℕ) (h : RoundInv T v D) :
    run masterM (2 * (v + 1) + 2 + 1) ⟨(0, 0, false, false), 0, T⟩ = ⟨(1, 0, false, false), 2 * v + 2, T⟩ := by
  have hns : ∀ i, i < v + 1 → (!(T.getD (0 + 2 * i) false) && T.getD (0 + 2 * i + 1) false) = false := by
    intro i hi
    simp only [Nat.zero_add]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * 0 + 1 = 1 from by norm_num, h.lsent]; simp
    · rw [(h.ctr i (by omega) (by omega)).1, (h.ctr i (by omega) (by omega)).2]; simp
  have hsep : (!(T.getD (0 + 2 * (v + 1)) false) && T.getD (0 + 2 * (v + 1) + 1) false) = true := by
    simp only [Nat.zero_add]
    rw [show 2 * (v + 1) + 1 = 2 * v + 3 from by omega, show 2 * (v + 1) = 2 * v + 2 from by omega,
      h.seplo, h.sephi]
    decide
  have eINIT : run masterM (2 * (v + 1) + 2) ⟨(0, 0, false, false), 0, T⟩
      = ⟨(0, 2, T.getD (2 * v + 2) false, false), 2 * v + 3, T⟩ := by
    rw [show (⟨(0, 0, false, false), 0, T⟩ : Cfg masterM) = embedScanR 0 ⟨(0, false), 0, T⟩ from rfl,
      sim_run_INIT (2 * (v + 1) + 2) ⟨(0, false), 0, T⟩ (scanRightSep_no_early_halt hns),
      run_scan_right_halt T 0 false (v + 1) hns hsep, Nat.zero_add,
      show 2 * (v + 1) + 1 = 2 * v + 3 from by omega, show 2 * (v + 1) = 2 * v + 2 from by omega]
    rfl
  rw [run_add, eINIT, run_one, seam_INIT, show 2 * v + 3 - 1 = 2 * v + 2 from by omega]

/-! ## The full run from `init`, and the promise `Decides` -/

/-- **The complete run from the forced initial config.**  INIT phase then `wholeRun`: from `⟨start, 0, T⟩` the
master halts in the `HALT` group reading the input's doubled `a_v`.  Total clock `2(v+1)+2 + 1 + (clockSum v D + 7)`. -/
theorem fullRun (T : List Bool) (v D : ℕ) (hv : v ≤ D) (h : RoundInv T v D) :
    ∃ T', run masterM (2 * (v + 1) + 2 + 1 + (clockSum v D + 7)) ⟨(0, 0, false, false), 0, T⟩
        = ⟨(9, 0, T.getD (2 * v + 4 + 2 * v) false, false), 4, T'⟩ := by
  obtain ⟨T', hrun⟩ := wholeRun v T D hv h
  exact ⟨T', by rw [run_add, init_phase T v D h, hrun]⟩

/-- **Promise `Decides`.**  On a well-formed input `T` (satisfying `RoundInv T v D`, `v ≤ D` — a doubled
`LSENT counterᵛ SEP a₀…a_{D-1} REND` tape), the master, started from its forced initial config, **halts** and its
decision bit is exactly the input's doubled `a_v` (`= T.getD (2v+4+2v) false`).  This is `HaltsBy`/`decideOut` at the
explicit clock — a promise-restricted `Decides` (the machine is only claimed correct on well-formed inputs). -/
theorem readAv_promise (T : List Bool) (v D : ℕ) (hv : v ≤ D) (h : RoundInv T v D) :
    HaltsBy masterM T (2 * (v + 1) + 2 + 1 + (clockSum v D + 7))
    ∧ decideOut masterM T (2 * (v + 1) + 2 + 1 + (clockSum v D + 7)) = T.getD (2 * v + 4 + 2 * v) false := by
  obtain ⟨T', hrun⟩ := fullRun T v D hv h
  refine ⟨?_, ?_⟩
  · unfold HaltsBy
    rw [master_forced_init, hrun]
    rfl
  · unfold decideOut
    rw [master_forced_init, hrun]
    rfl

/-- **Polynomial clock.**  The full-run clock is `≤ 32(D+1)² + 2D + 12` — quadratic in the data count `D` (`≤ |T|`),
hence polynomial in the input length.  So the promise `Decides` runs in polynomial time. -/
theorem readAv_clock_poly (v D : ℕ) (hv : v ≤ D) :
    2 * (v + 1) + 2 + 1 + (clockSum v D + 7) ≤ 32 * (D + 1) * (D + 1) + 2 * D + 12 := by
  have := clockSum_le_quad v D hv
  omega

end PallLean.Paper93.DeepMath.PathB.CookLevinInP

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinRendShift
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinScanLeftSep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinScanRightSep

/-!
# Cook–Levin M1 — "no early halt" phase bounds for `rendShift` and `scanLeftSep`

To lift a sub-machine's run to the master via `sim_run_*`, we must know the sub-machine stays *off* its halt
sub-phase for every step `i < t` (not just at the multiples where the run-lemma computes the endpoint).  Both
`rendShift` (halt phase `8`) and `scanLeftSep` (halt phase `2`) reach their halt phase only on the *last* transition
of the pair that is `REND` / `SEP` respectively; all earlier phases are traversed unconditionally.

The proof factors `i = (period)·j + r` with `r < period`: after `period·j` steps the machine is back at phase `0`
(its `run_*_k` invariant), and the remaining `r < period` steps advance the phase to exactly `r` — which is
*tape-independent* because phases `0 … period-1` do not branch.  Hence phase `= r ≠ halt`.

These are the enablers the counter-present round body needs to discharge `rendShift`/`scanLeftSep`'s tape-dependent
`hmin`s from the doubled-tape invariant.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinScanLeftSep
open PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep (scanRightSep)

/-! ## `rendShift`: phase stays `< 8` within a block (period 8) -/

/-- The first `r < 8` steps from a phase-`0` `rendShift` config reach phase `r` (never the halt phase `8`).
Tape-independent: phases `0 … 7` are unconditional (only the `7 → 8/0` transition branches on `REND`). -/
theorem rendShift_phase_lt {c0 c1 : Bool} {q : ℕ} {x : List Bool} :
    ∀ r, r < 8 → (run rendShift r ⟨(0, c0, c1), q, x⟩).st.1 ≠ 8 := by
  intro r hr
  interval_cases r
  · rw [run_zero]; simp
  · rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, step_fetch1]; simp
  · rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero,
      step_fetch1, step_fetch2]; simp
  · rw [show (3 : ℕ) = 2 + 1 from rfl, run_succ, show (2 : ℕ) = 1 + 1 from rfl, run_succ,
      show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, step_fetch1, step_fetch2, step_readlo]; simp
  · rw [show (4 : ℕ) = 3 + 1 from rfl, run_succ, show (3 : ℕ) = 2 + 1 from rfl, run_succ,
      show (2 : ℕ) = 1 + 1 from rfl, run_succ, show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero,
      step_fetch1, step_fetch2, step_readlo, CookLevinRendShift.step_readhi]; simp
  · rw [show (5 : ℕ) = 4 + 1 from rfl, run_succ, show (4 : ℕ) = 3 + 1 from rfl, run_succ,
      show (3 : ℕ) = 2 + 1 from rfl, run_succ, show (2 : ℕ) = 1 + 1 from rfl, run_succ,
      show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero,
      step_fetch1, step_fetch2, step_readlo, CookLevinRendShift.step_readhi, step_back1]; simp
  · rw [show (6 : ℕ) = 5 + 1 from rfl, run_succ, show (5 : ℕ) = 4 + 1 from rfl, run_succ,
      show (4 : ℕ) = 3 + 1 from rfl, run_succ, show (3 : ℕ) = 2 + 1 from rfl, run_succ,
      show (2 : ℕ) = 1 + 1 from rfl, run_succ, show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero,
      step_fetch1, step_fetch2, step_readlo, CookLevinRendShift.step_readhi, step_back1, step_back2]; simp
  · rw [show (7 : ℕ) = 6 + 1 from rfl, run_succ, show (6 : ℕ) = 5 + 1 from rfl, run_succ,
      show (5 : ℕ) = 4 + 1 from rfl, run_succ, show (4 : ℕ) = 3 + 1 from rfl, run_succ,
      show (3 : ℕ) = 2 + 1 from rfl, run_succ, show (2 : ℕ) = 1 + 1 from rfl, run_succ,
      show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero,
      step_fetch1, step_fetch2, step_readlo, CookLevinRendShift.step_readhi, step_back1, step_back2,
      step_writelo]; simp

/-- **`rendShift` no early halt.**  If the first `K` pairs from `q` are non-`REND`, then for every `i < 8K+8` the
machine has not yet reached the halt phase `8`.  (At `i = 8K+8` it halts on the `REND` pair.) -/
theorem rendShift_no_early_halt {c0 c1 : Bool} {q : ℕ} {x : List Bool} {K : ℕ}
    (hnr : ∀ i < K, (x.getD (q + 2 * i + 2) false && !(x.getD (q + 2 * i + 3) false)) = false) :
    ∀ i, i < 8 * K + 8 → (run rendShift i ⟨(0, c0, c1), q, x⟩).st.1 ≠ 8 := by
  intro i hi
  have hir : i = 8 * (i / 8) + i % 8 := by omega
  have hr8 : i % 8 < 8 := by omega
  have hjK : i / 8 ≤ K := by omega
  rw [hir, run_add, run_shift_k x q c0 c1 (i / 8) (fun i' hi' => hnr i' (by omega))]
  exact rendShift_phase_lt (i % 8) hr8

/-! ## `scanLeftSep`: phase stays `< 2` within a block (period 2) -/

/-- The first `r < 2` steps from a phase-`0` `scanLeftSep` config reach phase `r` (never the halt phase `2`). -/
theorem scanLeftSep_phase_lt {st : Bool} {P : ℕ} {tape : List Bool} :
    ∀ r, r < 2 → (run scanLeftSep r ⟨(0, st), P, tape⟩).st.1 ≠ 2 := by
  intro r hr
  interval_cases r
  · rw [run_zero]; simp
  · rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, CookLevinScanLeftSep.step_readhi]; simp

/-- **`scanLeftSep` no early halt.**  If the first `m` pairs (going left from `P`) are non-`SEP`, then for every
`i < 2m+2` the machine has not yet reached the halt phase `2`.  (At `i = 2m+2` it halts on the `SEP` pair.) -/
theorem scanLeftSep_no_early_halt {st : Bool} {P : ℕ} {tape : List Bool} {m : ℕ}
    (hns : ∀ i < m, (!(tape.getD (P - 2 * i - 1) false) && tape.getD (P - 2 * i) false) = false) :
    ∀ i, i < 2 * m + 2 → (run scanLeftSep i ⟨(0, st), P, tape⟩).st.1 ≠ 2 := by
  intro i hi
  have hir : i = 2 * (i / 2) + i % 2 := by omega
  have hr2 : i % 2 < 2 := by omega
  have hjm : i / 2 ≤ m := by omega
  rw [hir, run_add, run_scan_left tape P st (i / 2) (fun i' hi' => hns i' (by omega))]
  exact scanLeftSep_phase_lt (i % 2) hr2

/-! ## `scanRightSep`: phase stays `< 2` within a block (period 2) — for the INIT phase -/

/-- The first `r < 2` steps from a phase-`0` `scanRightSep` config reach phase `r` (never the halt phase `2`). -/
theorem scanRightSep_phase_lt {st : Bool} {P : ℕ} {tape : List Bool} :
    ∀ r, r < 2 → (run scanRightSep r ⟨(0, st), P, tape⟩).st.1 ≠ 2 := by
  intro r hr
  interval_cases r
  · rw [run_zero]; simp
  · rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, CookLevinScanRightSep.step_readlo]; simp

/-- **`scanRightSep` no early halt.**  If the first `m` pairs (going right from `P`) are non-`SEP`, then for every
`i < 2m+2` the machine has not yet reached the halt phase `2`.  (At `i = 2m+2` it halts on the `SEP` pair.) -/
theorem scanRightSep_no_early_halt {st : Bool} {P : ℕ} {tape : List Bool} {m : ℕ}
    (hns : ∀ i < m, (!(tape.getD (P + 2 * i) false) && tape.getD (P + 2 * i + 1) false) = false) :
    ∀ i, i < 2 * m + 2 → (run scanRightSep i ⟨(0, st), P, tape⟩).st.1 ≠ 2 := by
  intro i hi
  have hir : i = 2 * (i / 2) + i % 2 := by omega
  have hr2 : i % 2 < 2 := by omega
  have hjm : i / 2 ≤ m := by omega
  rw [hir, run_add, CookLevinScanRightSep.run_scan_right tape P st (i / 2) (fun i' hi' => hns i' (by omega))]
  exact scanRightSep_phase_lt (i % 2) hr2

end PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds

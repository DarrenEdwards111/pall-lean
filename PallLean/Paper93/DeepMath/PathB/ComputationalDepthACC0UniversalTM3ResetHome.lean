import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Seek
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Move

/-!
# Entry 408 — universal-TM-table build: the config-home reset `resetToHome3` (proved)

The rule-table match loop (entry 409+) tries each encoded record's key against the configuration key in turn.  Each
attempt (`recordKeyMatch3`, entry 407) runs the marker shuttle out to the record and back, so it leaves the head on the
**config side** but at a *data-dependent* position — `c + min(a,bᵢ)` (state mismatch) or `c+a+1` (symbol stage).  Before
the next record can be tried, the head must be returned to the config key start `c`.

A data-dependent leftward move cannot be done by a fixed-length corridor (the distance is not known statically); it needs
a **marker-based seek**.  This brick is that reset: assuming a persistent *home* marker sits at `home = c-1` (one cell
left of the config key), `resetToHome3` seeks left to it (`seekMarkLeft`, distance-independently) and then steps one cell
right, landing the head back at `c = home+1`, tape unchanged.

## What is proved (clean axioms, no `sorry`)

* **`resetToHome3 s found cont out`** — `seekMarkLeft s found cont ++ moveRight3 found out`.
* **`resetToHome3_run`** (PROVED) — with the home marker at `home` (`tp.getD home O = M`), no marker in `(home, home+d]`,
  and `home+d < tp.length`: `∃ N, reachIn (toNTM3 (resetToHome3 …)) N (s, home + d, tp) (out, home + 1, tp)` — from any
  head position `home+d` in the config window the machine returns to `home+1`, the tape identical.

## Honest scope

This is the **inter-record head reset** for the table loop — a distance-independent return to the config home, the one
piece the loop needs beyond the per-record matcher.  It does **not** yet thread it into the table loop, nor apply the
matched rule.  Note the loop that uses this must maintain the home marker, so the matcher's no-marker hypothesis will
need to be *windowed* (no marker only in the cells it shuttles through) — that refactor and the loop assembly are the
genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek (seekMarkLeft seekMarkLeft_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The config-home reset.**  Seek left to the home marker, then step one cell right onto the config key start. -/
def resetToHome3 (s found cont out : ℕ) : TMachine3 :=
  seekMarkLeft s found cont ++ moveRight3 found out

/-- **The config-home reset run (PROVED).**  From any head position `home + d` in the config window, return to
`home + 1`, tape unchanged. -/
theorem resetToHome3_run (s found cont out home d : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M)
    (hno : ∀ k, 0 < k → k ≤ d → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hbound : home + d < tp.length) :
    ∃ N, reachIn (toNTM3 (resetToHome3 s found cont out)) N (s, home + d, tp) (out, home + 1, tp) := by
  obtain ⟨N, hseek⟩ := seekMarkLeft_run s found cont home tp hmark d hno hbound
  have hmr := moveRight3_run_eq found out home tp (by omega)
  exact ⟨N + 1, reachIn_seq3 (seekMarkLeft s found cont) (moveRight3 found out) N 1 _ _ _ hseek hmr⟩

/-!
**The config-home reset, proved.**  `resetToHome3` returns the head distance-independently to the config key start `c =
home+1`, the reusable inter-record reset for the table loop.  Next: window the matcher's no-marker hypothesis so the home
marker is tolerated, then thread the matcher + this reset into the rule-table match loop `matchTable3` — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome.resetToHome3_run

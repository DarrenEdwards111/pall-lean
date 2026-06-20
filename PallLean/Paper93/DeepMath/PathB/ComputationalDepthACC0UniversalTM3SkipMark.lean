import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Seek

/-!
# Entry 432 — universal-TM-table build: skip a marker leftward `skipMarkLeft3` (proved)

The assembly hit a genuine coherence conflict: with a single marker symbol `M`, the *home* marker (for config navigation,
at `c-1`) and the simulated *head* marker (in the tape) are indistinguishable, so a leftward seek from inside the tape
stops at the head marker, not the home marker.  The clean single-symbol resolution is to **skip** the head marker — seek
to it, step one cell past it — so a *second* leftward seek then reaches the home marker.

This brick is that skip: `seekMarkLeft` (entry 387) to the marker, then one `moveLeft3` (entry 386) off it.  Composing it
before `resetToHome3` lets the cache refresh navigate from inside the tape to the config home past the head marker.

## What is proved (clean axioms, no `sorry`)

* **`skipMarkLeft3 s found cont s'`** — `seekMarkLeft s found cont ++ moveLeft3 found s'`.
* **`skipMarkLeft3_run`** (PROVED) — with the marker at `p`, no marker in `(p, p+d]`, `p+d < tp.length`: `∃ N, reachIn N
  (s, p+d, tp) (s', p-1, tp)` — from any position `p+d` right of the marker, the head ends just left of it (`p-1`), the
  tape identical.

## Honest scope

This is the **skip-a-marker** primitive — the single-symbol tool that lets navigation pass the head marker to reach the
home marker.  It does **not** by itself assemble the cache refresh or the full simulated step / `EmitsEncodedStep3`.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipMark

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek (seekMarkLeft seekMarkLeft_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Skip a marker leftward.**  Seek left to the marker, then step one cell past it. -/
def skipMarkLeft3 (s found cont s' : ℕ) : TMachine3 :=
  seekMarkLeft s found cont ++ moveLeft3 found s'

/-- **The skip-a-marker run (PROVED).**  From any position `p+d` right of the marker at `p`, end just left of it (`p-1`),
tape identical. -/
theorem skipMarkLeft3_run (s found cont s' p d : ℕ) (tp : List Sym3) (hmark : tp.getD p Sym3.O = Sym3.M)
    (hno : ∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M) (hbnd : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (skipMarkLeft3 s found cont s')) N (s, p + d, tp) (s', p - 1, tp) := by
  obtain ⟨N1, h1⟩ := seekMarkLeft_run s found cont p tp hmark d hno hbnd
  have h2 := moveLeft3_run_eq found s' p tp (by omega)
  exact ⟨N1 + 1, reachIn_seq3 (seekMarkLeft s found cont) (moveLeft3 found s') N1 1 _ _ _ h1 h2⟩

/-!
**Skip a marker leftward, proved.**  `skipMarkLeft3` seeks to a marker and steps past it — the single-symbol tool to
navigate past the head marker toward the home marker, resolving the two-marker conflict.  Next: chain it before
`resetToHome3` for the cache refresh, then assemble the full simulated step toward `EmitsEncodedStep3` — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipMark

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipMark.skipMarkLeft3_run

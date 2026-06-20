import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MoveN
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Seek
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Unmark

/-!
# Entry 402 — universal-TM-table build: the marker-shuttle return-and-restore `probeTail3` (proved)

The marker compare shuttles the head out to a distant rule-key cell, tests it, and must then **return to the anchor and
restore it** — the distance-independent half of the shuttle.  This brick is that tail: `seekMarkLeft` walks left to the
marker `M` (regardless of how far the outbound trip went), then `unmark3` overwrites the marker with the carried bit `b`,
restoring the cell.  This is where the marker route's distance-independence is realised: the return needs no step count.

## What is proved (clean axioms, no `sorry`)

* **`probeTail3 sIn sFound sCont sOut b`** — `seekMarkLeft sIn sFound sCont ++ unmark3 sFound sOut b`.
* **`probeTail3_run`** (PROVED) — with the marker at `p` (`tp.getD p O = M`), no marker in `(p, p+d]`, and `p+d` in
  bounds: `∃ N, reachIn (toNTM3 (probeTail3 …)) N (sIn, p+d, tp) (sOut, p, writeAt3 tp p b)` — the head returns from the
  distant cell `p+d` to the anchor `p` and restores it to `b`, ending in `sOut`.

## Honest scope

This is the **return-and-restore tail** of the marker shuttle.  It does **not** yet do the outbound move, nor the test,
nor the full compare.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ProbeTail

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek (seekMarkLeft seekMarkLeft_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The return-and-restore tail.**  Seek left to the marker, then overwrite it with the carried bit `b`. -/
def probeTail3 (sIn sFound sCont sOut : ℕ) (b : Sym3) : TMachine3 :=
  seekMarkLeft sIn sFound sCont ++ unmark3 sFound sOut b

/-- **The return-and-restore run (PROVED).**  From the distant cell `p+d`, walk left to the marker at `p` and restore it
to `b`, ending at `p` in state `sOut`. -/
theorem probeTail3_run (sIn sFound sCont sOut p d : ℕ) (b : Sym3) (tp : List Sym3)
    (hmark : tp.getD p Sym3.O = Sym3.M) (hno : ∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M)
    (hbound : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (probeTail3 sIn sFound sCont sOut b)) N (sIn, p + d, tp) (sOut, p, writeAt3 tp p b) := by
  obtain ⟨N, hseek⟩ := seekMarkLeft_run sIn sFound sCont p tp hmark d hno hbound
  have hseek' := reachIn_append_left3 (seekMarkLeft sIn sFound sCont) (unmark3 sFound sOut b) N _ _ hseek
  have hun := unmark3_run sFound sOut b p tp
  have hun' := reachIn_append_right3 (seekMarkLeft sIn sFound sCont) (unmark3 sFound sOut b) 1 _ _ hun
  exact ⟨N + 1, (reachIn_add (toNTM3 (probeTail3 sIn sFound sCont sOut b)) N 1 _ _).mpr ⟨_, hseek', hun'⟩⟩

/-!
**The return-and-restore tail, proved.**  `probeTail3` realises the distance-independent return: `seekMarkLeft` finds the
anchor regardless of the outbound distance, and `unmark3` restores the carried bit.  Next: prepend the outbound move and
the test to obtain the full single-bit compare-after-mark — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ProbeTail

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ProbeTail.probeTail3_run

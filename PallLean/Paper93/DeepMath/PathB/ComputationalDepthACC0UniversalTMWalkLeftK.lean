import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMFillConst

/-!
# Entry 362 — universal-TM-table build: the fixed-distance left walk `walkLeftK` (proved)

`walkRightK` (entry 357) walks the head right a fixed distance ending in a controlled state.  The block-copy of the
apply phase needs the **return** trip: after copying a source cell into a destination region, the head must travel back
left to the next source cell.  `walkLeftK k s` walks the head left exactly `k` cells through the states `s, …, s+k`,
ending in state `s+k` at head `h-k`, preserving the tape — the left analog of `walkRightK`, a `reachIn_seq` fold of
`moveLeft`s.

## What is proved (clean axioms, no `sorry`)

* **`walkLeftK k s`** — recursively, `0 ↦ []` and `k+1 ↦ moveLeft s (s+1) ++ walkLeftK k (s+1)`: one `moveLeft` per
  cell, advancing the control state each step.
* **`walkLeftK_run`** (PROVED) — `∃ tp', reachIn (toNTM (walkLeftK k s)) k (s, h, tp) (s+k, h-k, tp') ∧
  ∀ q, tp'.getD q false = tp.getD q false`: the walk runs `k` steps to state `s+k` at head `h-k`, preserving the tape.

## Honest scope

This is the **fixed-distance left walk** — the return-trip primitive completing the head-motion-by-distance pair
(`walkRightK`/`walkLeftK`).  It does **not** yet assemble the block copy (copy a field cell-by-cell with `copyBit` and a
`walkLeftK` return), nor the full apply, nor the rule-table loop.  Building those fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMoveLeft (moveLeft moveLeft_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The fixed-distance left walk.**  One `moveLeft` per cell, advancing the state each step; from `s` it reaches
`s+k` after walking `k` cells left. -/
def walkLeftK : ℕ → ℕ → TMachine
  | 0, _ => []
  | k + 1, s => moveLeft s (s + 1) ++ walkLeftK k (s + 1)

/-- **The fixed-distance left walk run (PROVED).**  `walkLeftK k s` runs `k` steps from `(s, h, tp)` to
`(s+k, h-k, tp')`, preserving the tape. -/
theorem walkLeftK_run (k s h : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (walkLeftK k s)) k (s, h, tp) (s + k, h - k, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  induction k generalizing s h tp with
  | zero => exact ⟨tp, rfl, fun _ => rfl⟩
  | succ k ih =>
      obtain ⟨tp1, run1, p1⟩ := moveLeft_run_pres s (s + 1) h tp
      obtain ⟨tp2, run2, p2⟩ := ih (s + 1) (h - 1) tp1
      refine ⟨tp2, ?_, fun q => (p2 q).trans (p1 q)⟩
      have comp := reachIn_seq (moveLeft s (s + 1)) (walkLeftK k (s + 1)) 1 k _ _ _ run1 run2
      convert comp using 1
      · omega
      · rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, by omega, rfl⟩

/-!
**The fixed-distance left walk, proved.**  `walkLeftK k s` returns the head `k` cells left ending in a controlled state,
preserving the tape — completing the `walkRightK`/`walkLeftK` motion pair.  Next: the block copy (copy a field
cell-by-cell, `copyBit` forward then `walkLeftK` back), the full apply, and the rule-table loop — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK.walkLeftK_run

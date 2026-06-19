import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareAdjacentNe

/-!
# Entry 357 — universal-TM-table build: the fixed-distance walk `walkRightK` (proved)

The two-cell comparison `compareAdjacent` (entries 355–356) compares cells at offsets `j` and `j+1`.  The real key
match compares cells in two *separated* regions, so after carrying a bit the head must travel a known distance to reach
the other operand.  Entry-334's `walkRight` is a single-state self-loop (it stays in state `0`); to chain a walk *into*
a subsequent comparison we need a walk that ends in a **controlled distinct state**.

`walkRightK k s` walks the head right exactly `k` cells through the states `s, s+1, …, s+k`, ending in state `s+k` at
head `h+k`, preserving the tape — a `reachIn_seq` fold of `scanBit`s, the gap-traversal primitive for distant
comparison.

## What is proved (clean axioms, no `sorry`)

* **`walkRightK k s`** — recursively, `0 ↦ []` and `k+1 ↦ scanBit s (s+1) ++ walkRightK k (s+1)`: one `scanBit` per
  cell, advancing the control state each step.
* **`walkRightK_run`** (PROVED) — `∃ tp', reachIn (toNTM (walkRightK k s)) k (s, h, tp) (s+k, h+k, tp') ∧
  ∀ q, tp'.getD q false = tp.getD q false`: the walk runs `k` steps to state `s+k` at head `h+k`, preserving the tape.

## Honest scope

This is the **fixed-distance walk** ending in a controlled state — the gap-traversal piece a distant-region comparison
chains between the carry and the compare.  It does **not** yet assemble the distant comparison itself (carry a bit, walk
to the other region, compare, with a round-trip head invariant), nor the rule-table scan-and-match loop, nor the apply.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit scanBit_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The fixed-distance right walk.**  One `scanBit` per cell, advancing the state each step; from `s` it reaches
`s+k` after walking `k` cells right. -/
def walkRightK : ℕ → ℕ → TMachine
  | 0, _ => []
  | k + 1, s => scanBit s (s + 1) ++ walkRightK k (s + 1)

/-- **The fixed-distance walk run (PROVED).**  `walkRightK k s` runs `k` steps from `(s, h, tp)` to `(s+k, h+k, tp')`,
preserving the tape. -/
theorem walkRightK_run (k s h : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (walkRightK k s)) k (s, h, tp) (s + k, h + k, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  induction k generalizing s h tp with
  | zero => exact ⟨tp, rfl, fun _ => rfl⟩
  | succ k ih =>
      obtain ⟨tp1, run1, p1⟩ := scanBit_run_pres s (s + 1) h tp
      obtain ⟨tp2, run2, p2⟩ := ih (s + 1) (h + 1) tp1
      refine ⟨tp2, ?_, fun q => (p2 q).trans (p1 q)⟩
      have comp := reachIn_seq (scanBit s (s + 1)) (walkRightK k (s + 1)) 1 k _ _ _ run1 run2
      convert comp using 1
      · omega
      · rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, by omega, rfl⟩

/-!
**The fixed-distance walk, proved.**  `walkRightK k s` traverses a known gap of `k` cells ending in a controlled state
`s+k`, preserving the tape — the piece a distant-region comparison chains between carrying a bit and comparing.  Next:
the distant comparison (carry, `walkRightK` to the other region, compare, round-trip invariant), the rule-table
scan-and-match loop, and the apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK.walkRightK_run

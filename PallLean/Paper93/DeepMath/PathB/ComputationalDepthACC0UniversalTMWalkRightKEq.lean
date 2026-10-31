import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMBranchCheckEq

/-!
# Entry 374 — universal-TM-table build: the list-preserving fixed-distance walk `walkRightK_run_eq` (proved)

`walkRightK_run` (entry 357) walks `k` cells right but only `getD`-preserves the tape.  The list-preserving comparison
composites (next) need the walk to leave the tape *identical*.  Since `walkRightK` is a fold of `scanBit`s, and
`scanBit_run_eq` (entry 370) leaves the tape identical in bounds, the whole walk does too.

## What is proved (clean axioms, no `sorry`)

* **`walkRightK_run_eq`** (PROVED) — `h + k ≤ tp.length → reachIn (toNTM (walkRightK k s)) k (s, h, tp) (s+k, h+k, tp)`:
  the fixed-distance right walk returning the *identical* tape (all walked positions in bounds).

## Honest scope

This is the **list-preserving fixed-distance walk** — the walk returns the same tape list under an in-bounds
hypothesis.  It does **not** yet compose into a list-preserving `compareDistant`, nor the key comparison, nor the
rule-table scan-and-match.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightKEq

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK (walkRightK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanListPres (scanBit_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The fixed-distance right walk, list-preserving (PROVED).**  With all walked positions in bounds, `walkRightK k s`
returns the *identical* tape. -/
theorem walkRightK_run_eq (k s h : ℕ) (tp : List Bool) (hbound : h + k ≤ tp.length) :
    reachIn (toNTM (walkRightK k s)) k (s, h, tp) (s + k, h + k, tp) := by
  induction k generalizing s h with
  | zero => exact rfl
  | succ k ih =>
      have run1 := scanBit_run_eq s (s + 1) h tp (by omega)
      have run2 := ih (s + 1) (h + 1) (by omega)
      have comp := reachIn_seq (scanBit s (s + 1)) (walkRightK k (s + 1)) 1 k _ _ _ run1 run2
      convert comp using 1
      · omega
      · rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, by omega, rfl⟩

/-!
**The list-preserving fixed-distance walk, proved.**  `walkRightK_run_eq` returns the identical tape after walking `k`
cells, since each `scanBit` step is the identity in bounds.  Next: the list-preserving `compareDistant`, then the key
comparison and the rule-table scan-and-match — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightKEq

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightKEq.walkRightK_run_eq

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMWriteConst

/-!
# Entry 360 — universal-TM-table build: the inter-region bit copy `copyBit` (proved)

`compareDistant` (entry 358) *reads* a bit in one region and *compares* it against another.  The apply phase needs the
dual: *read* a bit in one region and *write* it into another.  `copyBit` does exactly that — it carries cell `j`'s value
in the control state (`branchBit`), walks `m` cells to region B (`walkRightK`), and **writes the carried value** there
(`writeConst`), copying cell `j` to cell `j+m`.

It is `compareDistant` with the final `checkBit` (compare) replaced by `writeConst` (overwrite) — the move that
transplants a digit of the matched rule's right-hand side into the encoded configuration.

## What is proved (clean axioms, no `sorry`)

* **`copyBit m s sT0 sF0 E`** — `branchBit s sT0 sF0 ++ ((walkRightK m sT0 ++ writeConst true (sT0+m) E) ++
  (walkRightK m sF0 ++ writeConst false (sF0+m) E))`: carry cell `j`, walk `m` on the matching track, write the carried
  value at `j+m`, converge to `E`.
* **`copyBit_run`** (PROVED) — `∃ tp', reachIn (toNTM (copyBit m s sT0 sF0 E)) (m+2) (s, j, tp) (E, j+m+1, tp') ∧
  tp'.getD (j+m) false = tp.getD j false ∧ ∀ q, q ≠ j+m → tp'.getD q false = tp.getD q false`: the copy runs `m+2` steps
  to `E`, with cell `j+m` now holding cell `j`'s value and every other cell unchanged.

## Honest scope

This is the **inter-region bit copy** — the apply's transplant operation, with a full specification (the target cell
holds the source value, all others unchanged).  It does **not** yet assemble the full apply (copy the whole new state
and symbol of the matched rule into the configuration), nor the rule-table scan-and-match loop.  Building those fragment
by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBit

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM writeAt)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch (branchBit branchBit_run_true branchBit_run_false)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK (walkRightK walkRightK_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteConst (writeConst writeConst_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left reachIn_append_right)

/-- **The inter-region bit copy machine.**  Carry cell `j` (`branchBit`), walk `m` cells to region B on the matching
track, write the carried value at `j+m` (`writeConst`), converging to `E`. -/
def copyBit (m s sT0 sF0 E : ℕ) : TMachine :=
  branchBit s sT0 sF0 ++
    ((walkRightK m sT0 ++ writeConst true (sT0 + m) E) ++
     (walkRightK m sF0 ++ writeConst false (sF0 + m) E))

/-- **The inter-region bit copy run (PROVED).**  `copyBit m s sT0 sF0 E` runs `m+2` steps from `(s, j, tp)` to
`(E, j+m+1, tp')`, with cell `j+m` now holding cell `j`'s value and every other cell unchanged. -/
theorem copyBit_run (m s sT0 sF0 E j : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (copyBit m s sT0 sF0 E)) (m + 2) (s, j, tp) (E, j + m + 1, tp') ∧
      tp'.getD (j + m) false = tp.getD j false ∧
      ∀ q, q ≠ j + m → tp'.getD q false = tp.getD q false := by
  by_cases hb : tp.getD j false = true
  · -- carried `true`
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_true s sT0 sF0 j tp hb
    obtain ⟨tp2, runW, pW⟩ := walkRightK_run m sT0 j tp1
    have runC := writeConst_run true (sT0 + m) E (j + m) tp2
    refine ⟨writeAt tp2 (j + m) true, ?_, ?_, ?_⟩
    · have arm := reachIn_seq (walkRightK m sT0) (writeConst true (sT0 + m) E) m 1 _ _ _ runW runC
      have ver := reachIn_append_left (walkRightK m sT0 ++ writeConst true (sT0 + m) E)
        (walkRightK m sF0 ++ writeConst false (sF0 + m) E) (m + 1) _ _ arm
      have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
      convert full using 1
      omega
    · rw [writeAt_getD, if_pos rfl]; exact hb.symm
    · intro q hq; rw [writeAt_getD, if_neg hq, pW q, p1 q]
  · -- carried `false`
    have hbf : tp.getD j false = false := by rw [Bool.not_eq_true] at hb; exact hb
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_false s sT0 sF0 j tp hbf
    obtain ⟨tp2, runW, pW⟩ := walkRightK_run m sF0 j tp1
    have runC := writeConst_run false (sF0 + m) E (j + m) tp2
    refine ⟨writeAt tp2 (j + m) false, ?_, ?_, ?_⟩
    · have arm := reachIn_seq (walkRightK m sF0) (writeConst false (sF0 + m) E) m 1 _ _ _ runW runC
      have ver := reachIn_append_right (walkRightK m sT0 ++ writeConst true (sT0 + m) E)
        (walkRightK m sF0 ++ writeConst false (sF0 + m) E) (m + 1) _ _ arm
      have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
      convert full using 1
      omega
    · rw [writeAt_getD, if_pos rfl]; exact hbf.symm
    · intro q hq; rw [writeAt_getD, if_neg hq, pW q, p1 q]

/-!
**The inter-region bit copy, proved.**  `copyBit` transplants cell `j` into cell `j+m`, leaving everything else
untouched — `compareDistant` with its `checkBit` replaced by `writeConst`, the apply's transplant operation.  Next: the
full apply (copy the matched rule's new state and symbol into the configuration), then the rule-table scan-and-match
loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBit.copyBit_run

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMWalkRightKEq

/-!
# Entry 375 — universal-TM-table build: the list-preserving distant comparison (proved)

`compareDistant` (entry 358) compares cell `j` with the distant cell `j+m`, but only `getD`-preserves the tape.  The
rule-table scan-and-match needs the comparison to leave the tape *identical* (so the apply re-reads the original).  Its
three components — `branchBit` (carry), `walkRightK` (walk), `checkBit` (compare) — all now have list-preserving runs
(entries 373/374), and they all run on the *same* tape, so the whole comparison is list-preserving.

## What is proved (clean axioms, no `sorry`)

* **`compareDistant_run_eq`** (PROVED) — if cells `j`, `j+m` agree and `j+m < tp.length`, then
  `reachIn (toNTM (compareDistant m s sT0 sF0 E N)) (m+2) (s, j, tp) (E, j+m+1, tp)`: reaches the equal-state `E`
  leaving the tape *identical*.
* **`compareDistant_run_ne`** (PROVED) — if cells `j`, `j+m` differ and `j+m < tp.length`, then
  `reachIn (toNTM (compareDistant m s sT0 sF0 E N)) (m+2) (s, j, tp) (N, j+m+1, tp)`: reaches the not-equal state `N`
  leaving the tape *identical*.

## Honest scope

This is the **list-preserving distant comparison** — both outcomes, returning the same tape.  It does **not** yet
assemble the multi-bit key comparison (which needs the concrete configuration layout), nor the rule-table scan-and-match
loop, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistantEq

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch (branchBit)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit (checkBit)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK (walkRightK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistant (compareDistant)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranchCheckEq
  (branchBit_run_true_eq branchBit_run_false_eq checkBit_run_match_eq checkBit_run_fail_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightKEq (walkRightK_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left reachIn_append_right)

/-- **The distant comparison reaches `E` on equal cells, list-preserving (PROVED).** -/
theorem compareDistant_run_eq (m s sT0 sF0 E N j : ℕ) (tp : List Bool)
    (heq : tp.getD j false = tp.getD (j + m) false) (hbound : j + m < tp.length) :
    reachIn (toNTM (compareDistant m s sT0 sF0 E N)) (m + 2) (s, j, tp) (E, j + m + 1, tp) := by
  by_cases hb : tp.getD j false = true
  · have hjm : tp.getD (j + m) false = true := by rw [← heq]; exact hb
    have run1 := branchBit_run_true_eq s sT0 sF0 j tp hb (by omega)
    have runW := walkRightK_run_eq m sT0 j tp (by omega)
    have runC := checkBit_run_match_eq true (sT0 + m) E N (j + m) tp hjm (by omega)
    have arm := reachIn_seq (walkRightK m sT0) (checkBit true (sT0 + m) E N) m 1 _ _ _ runW runC
    have ver := reachIn_append_left (walkRightK m sT0 ++ checkBit true (sT0 + m) E N)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) E N) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega
  · have hbf : tp.getD j false = false := by rw [Bool.not_eq_true] at hb; exact hb
    have hjm : tp.getD (j + m) false = false := by rw [← heq]; exact hbf
    have run1 := branchBit_run_false_eq s sT0 sF0 j tp hbf (by omega)
    have runW := walkRightK_run_eq m sF0 j tp (by omega)
    have runC := checkBit_run_match_eq false (sF0 + m) E N (j + m) tp hjm (by omega)
    have arm := reachIn_seq (walkRightK m sF0) (checkBit false (sF0 + m) E N) m 1 _ _ _ runW runC
    have ver := reachIn_append_right (walkRightK m sT0 ++ checkBit true (sT0 + m) E N)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) E N) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega

/-- **The distant comparison reaches `N` on differing cells, list-preserving (PROVED).** -/
theorem compareDistant_run_ne (m s sT0 sF0 E N j : ℕ) (tp : List Bool)
    (hne : tp.getD j false ≠ tp.getD (j + m) false) (hbound : j + m < tp.length) :
    reachIn (toNTM (compareDistant m s sT0 sF0 E N)) (m + 2) (s, j, tp) (N, j + m + 1, tp) := by
  by_cases hb : tp.getD j false = true
  · have hjm : tp.getD (j + m) false = !true := by
      have h2 : tp.getD (j + m) false ≠ true := fun hc => hne (hb.trans hc.symm)
      simpa using h2
    have run1 := branchBit_run_true_eq s sT0 sF0 j tp hb (by omega)
    have runW := walkRightK_run_eq m sT0 j tp (by omega)
    have runC := checkBit_run_fail_eq true (sT0 + m) E N (j + m) tp hjm (by omega)
    have arm := reachIn_seq (walkRightK m sT0) (checkBit true (sT0 + m) E N) m 1 _ _ _ runW runC
    have ver := reachIn_append_left (walkRightK m sT0 ++ checkBit true (sT0 + m) E N)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) E N) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega
  · have hbf : tp.getD j false = false := by rw [Bool.not_eq_true] at hb; exact hb
    have hjm : tp.getD (j + m) false = !false := by
      have h2 : tp.getD (j + m) false ≠ false := fun hc => hne (hbf.trans hc.symm)
      simpa using h2
    have run1 := branchBit_run_false_eq s sT0 sF0 j tp hbf (by omega)
    have runW := walkRightK_run_eq m sF0 j tp (by omega)
    have runC := checkBit_run_fail_eq false (sF0 + m) E N (j + m) tp hjm (by omega)
    have arm := reachIn_seq (walkRightK m sF0) (checkBit false (sF0 + m) E N) m 1 _ _ _ runW runC
    have ver := reachIn_append_right (walkRightK m sT0 ++ checkBit true (sT0 + m) E N)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) E N) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega

/-!
**The list-preserving distant comparison, proved.**  Both outcomes (`E` on equal, `N` on differing) return the
identical tape — every component runs on the same `tp`, so there is no transport.  Next: the multi-bit key comparison
(committing the configuration layout), then the rule-table scan-and-match loop and the apply — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistantEq

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistantEq.compareDistant_run_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistantEq.compareDistant_run_ne

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareBitReturn

/-!
# Entry 378 — universal-TM-table build: the three-way comparison step `compareStep3` (proved)

Comparing two unary fields for equality needs a *three-way* decision per cell pair: **continue** (both cells `true`, so
both fields are still running), **match-done** (both cells `false`, so both separators are aligned — the fields are
equal), or **no-match** (the cells differ).  The carry in `compareDistant` already splits on cell `j`'s value, so giving
the true-track and false-track *distinct* match-exits yields exactly these three outcomes:

* both `true` → `cont`,  both `false` → `matchSt`,  differ → `noMatch`.

## What is proved (clean axioms, no `sorry`)

* **`compareStep3 m s sT0 sF0 cont matchSt noMatch`** — `branchBit s sT0 sF0 ++ ((walkRightK m sT0 ++ checkBit true
  (sT0+m) cont noMatch) ++ (walkRightK m sF0 ++ checkBit false (sF0+m) matchSt noMatch))`.
* **`compareStep3_run_cont`** (PROVED) — both cells `true` ⇒ reaches `cont` at `j+m+1`, tape identical.
* **`compareStep3_run_match`** (PROVED) — both cells `false` ⇒ reaches `matchSt` at `j+m+1`, tape identical.
* **`compareStep3_run_ne`** (PROVED) — cells differ ⇒ reaches `noMatch` at `j+m+1`, tape identical.

## Honest scope

This is the **three-way comparison step** — the loop body of a unary-field equality test.  It does **not** yet loop it
(the unary-field equality comparison), nor the rule-table scan-and-match, nor the apply.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareStep3

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch (branchBit)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit (checkBit)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK (walkRightK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranchCheckEq
  (branchBit_run_true_eq branchBit_run_false_eq checkBit_run_match_eq checkBit_run_fail_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightKEq (walkRightK_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left reachIn_append_right)

/-- **The three-way comparison step.**  Carry cell `j`; on the `true` track a matching `j+m` continues (`cont`), on the
`false` track a matching `j+m` is the aligned separator (`matchSt`); a mismatch on either goes to `noMatch`. -/
def compareStep3 (m s sT0 sF0 cont matchSt noMatch : ℕ) : TMachine :=
  branchBit s sT0 sF0 ++
    ((walkRightK m sT0 ++ checkBit true (sT0 + m) cont noMatch) ++
     (walkRightK m sF0 ++ checkBit false (sF0 + m) matchSt noMatch))

/-- **Both cells `true` ⇒ continue (PROVED).** -/
theorem compareStep3_run_cont (m s sT0 sF0 cont matchSt noMatch j : ℕ) (tp : List Bool)
    (hj : tp.getD j false = true) (hjm : tp.getD (j + m) false = true) (hbound : j + m < tp.length) :
    reachIn (toNTM (compareStep3 m s sT0 sF0 cont matchSt noMatch)) (m + 2) (s, j, tp) (cont, j + m + 1, tp) := by
  have run1 := branchBit_run_true_eq s sT0 sF0 j tp hj (by omega)
  have runW := walkRightK_run_eq m sT0 j tp (by omega)
  have runC := checkBit_run_match_eq true (sT0 + m) cont noMatch (j + m) tp hjm (by omega)
  have arm := reachIn_seq (walkRightK m sT0) (checkBit true (sT0 + m) cont noMatch) m 1 _ _ _ runW runC
  have ver := reachIn_append_left (walkRightK m sT0 ++ checkBit true (sT0 + m) cont noMatch)
    (walkRightK m sF0 ++ checkBit false (sF0 + m) matchSt noMatch) (m + 1) _ _ arm
  have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
  convert full using 1
  omega

/-- **Both cells `false` ⇒ match-done (PROVED).** -/
theorem compareStep3_run_match (m s sT0 sF0 cont matchSt noMatch j : ℕ) (tp : List Bool)
    (hj : tp.getD j false = false) (hjm : tp.getD (j + m) false = false) (hbound : j + m < tp.length) :
    reachIn (toNTM (compareStep3 m s sT0 sF0 cont matchSt noMatch)) (m + 2) (s, j, tp) (matchSt, j + m + 1, tp) := by
  have run1 := branchBit_run_false_eq s sT0 sF0 j tp hj (by omega)
  have runW := walkRightK_run_eq m sF0 j tp (by omega)
  have runC := checkBit_run_match_eq false (sF0 + m) matchSt noMatch (j + m) tp hjm (by omega)
  have arm := reachIn_seq (walkRightK m sF0) (checkBit false (sF0 + m) matchSt noMatch) m 1 _ _ _ runW runC
  have ver := reachIn_append_right (walkRightK m sT0 ++ checkBit true (sT0 + m) cont noMatch)
    (walkRightK m sF0 ++ checkBit false (sF0 + m) matchSt noMatch) (m + 1) _ _ arm
  have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
  convert full using 1
  omega

/-- **Cells differ ⇒ no-match (PROVED).** -/
theorem compareStep3_run_ne (m s sT0 sF0 cont matchSt noMatch j : ℕ) (tp : List Bool)
    (hne : tp.getD j false ≠ tp.getD (j + m) false) (hbound : j + m < tp.length) :
    reachIn (toNTM (compareStep3 m s sT0 sF0 cont matchSt noMatch)) (m + 2) (s, j, tp) (noMatch, j + m + 1, tp) := by
  by_cases hb : tp.getD j false = true
  · have hjm : tp.getD (j + m) false = !true := by
      have h2 : tp.getD (j + m) false ≠ true := fun hc => hne (hb.trans hc.symm)
      simpa using h2
    have run1 := branchBit_run_true_eq s sT0 sF0 j tp hb (by omega)
    have runW := walkRightK_run_eq m sT0 j tp (by omega)
    have runC := checkBit_run_fail_eq true (sT0 + m) cont noMatch (j + m) tp hjm (by omega)
    have arm := reachIn_seq (walkRightK m sT0) (checkBit true (sT0 + m) cont noMatch) m 1 _ _ _ runW runC
    have ver := reachIn_append_left (walkRightK m sT0 ++ checkBit true (sT0 + m) cont noMatch)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) matchSt noMatch) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega
  · have hbf : tp.getD j false = false := by rw [Bool.not_eq_true] at hb; exact hb
    have hjm : tp.getD (j + m) false = !false := by
      have h2 : tp.getD (j + m) false ≠ false := fun hc => hne (hbf.trans hc.symm)
      simpa using h2
    have run1 := branchBit_run_false_eq s sT0 sF0 j tp hbf (by omega)
    have runW := walkRightK_run_eq m sF0 j tp (by omega)
    have runC := checkBit_run_fail_eq false (sF0 + m) matchSt noMatch (j + m) tp hjm (by omega)
    have arm := reachIn_seq (walkRightK m sF0) (checkBit false (sF0 + m) matchSt noMatch) m 1 _ _ _ runW runC
    have ver := reachIn_append_right (walkRightK m sT0 ++ checkBit true (sT0 + m) cont noMatch)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) matchSt noMatch) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega

/-!
**The three-way comparison step, proved.**  `compareStep3` routes a cell-pair comparison to continue / match-done /
no-match — the loop body of a unary-field equality test (both-`true` continue, both-`false` aligned-separator match,
differ no-match).  Next: loop it (the unary-field equality comparison), then the rule-table scan-and-match — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareStep3

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareStep3.compareStep3_run_cont
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareStep3.compareStep3_run_match
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareStep3.compareStep3_run_ne

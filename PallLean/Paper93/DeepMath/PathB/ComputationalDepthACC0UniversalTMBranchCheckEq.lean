import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanTable

/-!
# Entry 373 — universal-TM-table build: list-preserving branch/check runs (proved)

Just as the table scan needed *list*-preserving scanners (entries 370–372), the rule-table scan-and-match will need
list-preserving comparison primitives: the key comparison reads the tape, branches, and must leave the tape intact so
the next comparison (and the eventual apply) re-reads the original.  `branchBit` and `checkBit` both write back the
symbol they read, so by `writeAt_id_of_lt` (entry 369) each is the identity on the list at an in-bounds head.

## What is proved (clean axioms, no `sorry`)

* **`branchBit_run_true_eq` / `branchBit_run_false_eq`** (PROVED) — `h < tp.length` and the read symbol force the
  branch, leaving the tape *identical*: reading `true` reaches `(sTrue, h, tp)`, reading `false` reaches `(sFalse, h, tp)`.
* **`checkBit_run_match_eq` / `checkBit_run_fail_eq`** (PROVED) — `h < tp.length`: a cell equal to `b` reaches
  `(sCont, h+1, tp)`, a cell equal to `!b` reaches `(sFail, h+1, tp)`, in both cases the tape *identical*.

## Honest scope

These are the **list-preserving branch/check primitives** — the decision/comparison steps return the same tape list
under an in-bounds hypothesis.  They do **not** yet assemble a list-preserving key comparison, nor the rule-table
scan-and-match, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranchCheckEq

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM writeAt)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch (branchBit branchBit_step_true branchBit_step_false)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit (checkBit checkBit_step_match checkBit_step_fail)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteAtId (writeAt_id_of_lt)

/-- **`branchBit` on `true`, list-preserving (PROVED).** -/
theorem branchBit_run_true_eq (s sTrue sFalse h : ℕ) (tp : List Bool)
    (hb : tp.getD h false = true) (hbound : h < tp.length) :
    reachIn (toNTM (branchBit s sTrue sFalse)) 1 (s, h, tp) (sTrue, h, tp) := by
  have hstep := branchBit_step_true s sTrue sFalse h tp hb
  rw [show writeAt tp h true = tp from by rw [← hb]; exact writeAt_id_of_lt tp h hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-- **`branchBit` on `false`, list-preserving (PROVED).** -/
theorem branchBit_run_false_eq (s sTrue sFalse h : ℕ) (tp : List Bool)
    (hb : tp.getD h false = false) (hbound : h < tp.length) :
    reachIn (toNTM (branchBit s sTrue sFalse)) 1 (s, h, tp) (sFalse, h, tp) := by
  have hstep := branchBit_step_false s sTrue sFalse h tp hb
  rw [show writeAt tp h false = tp from by rw [← hb]; exact writeAt_id_of_lt tp h hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-- **`checkBit` on a match, list-preserving (PROVED).** -/
theorem checkBit_run_match_eq (b : Bool) (s sCont sFail h : ℕ) (tp : List Bool)
    (hb : tp.getD h false = b) (hbound : h < tp.length) :
    reachIn (toNTM (checkBit b s sCont sFail)) 1 (s, h, tp) (sCont, h + 1, tp) := by
  have hstep := checkBit_step_match b s sCont sFail h tp hb
  rw [show writeAt tp h b = tp from by rw [← hb]; exact writeAt_id_of_lt tp h hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-- **`checkBit` on a mismatch, list-preserving (PROVED).** -/
theorem checkBit_run_fail_eq (b : Bool) (s sCont sFail h : ℕ) (tp : List Bool)
    (hb : tp.getD h false = !b) (hbound : h < tp.length) :
    reachIn (toNTM (checkBit b s sCont sFail)) 1 (s, h, tp) (sFail, h + 1, tp) := by
  have hstep := checkBit_step_fail b s sCont sFail h tp hb
  rw [show writeAt tp h (!b) = tp from by rw [← hb]; exact writeAt_id_of_lt tp h hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-!
**The list-preserving branch/check primitives, proved.**  Under an in-bounds head, the decision/comparison steps return
the same tape list (each write-back is the identity, `writeAt_id_of_lt`).  Next: assemble a list-preserving key
comparison, then the rule-table scan-and-match, then the apply — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranchCheckEq

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranchCheckEq.branchBit_run_true_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranchCheckEq.checkBit_run_match_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranchCheckEq.checkBit_run_fail_eq

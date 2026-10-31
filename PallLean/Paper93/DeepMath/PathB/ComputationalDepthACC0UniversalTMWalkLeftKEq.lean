import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareDistantEq

/-!
# Entry 376 — universal-TM-table build: list-preserving left motions (proved)

The comparison *loop* (comparing two unary fields cell by cell) needs to return the head left between iterations.  The
return walk must leave the tape identical, so this brick gives list-preserving versions of the leftward motions:
`moveLeft` writes back what it reads, so it is the identity in bounds (`writeAt_id_of_lt`, entry 369), and `walkLeftK`
(a fold of `moveLeft`s) inherits this.

## What is proved (clean axioms, no `sorry`)

* **`moveLeft_run_eq`** (PROVED) — `h < tp.length → reachIn (toNTM (moveLeft s s')) 1 (s, h, tp) (s', h-1, tp)`: one
  leftward step leaving the tape *identical*.
* **`walkLeftK_run_eq`** (PROVED) — `h < tp.length → reachIn (toNTM (walkLeftK k s)) k (s, h, tp) (s+k, h-k, tp)`: the
  fixed-distance left walk leaving the tape *identical* (all written positions `≤ h < tp.length`).

## Honest scope

These are the **list-preserving left motions** — the return walk leaves the tape identical under an in-bounds
hypothesis.  They do **not** yet assemble the compare-and-return loop body, nor the unary-field equality comparison, nor
the rule-table scan-and-match.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMoveLeft (moveLeft moveLeft_step)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteAtId (writeAt_id_of_lt)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **`moveLeft` leaves the tape identical (PROVED).**  At an in-bounds head, the one-step leftward move returns the
same tape list. -/
theorem moveLeft_run_eq (s s' h : ℕ) (tp : List Bool) (hbound : h < tp.length) :
    reachIn (toNTM (moveLeft s s')) 1 (s, h, tp) (s', h - 1, tp) := by
  have hstep := moveLeft_step s s' h tp
  rw [writeAt_id_of_lt tp h hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-- **`walkLeftK` leaves the tape identical (PROVED).**  With the head in bounds (so all written positions are
`≤ h < tp.length`), the fixed-distance left walk returns the same tape list. -/
theorem walkLeftK_run_eq (k s h : ℕ) (tp : List Bool) (hbound : h < tp.length) :
    reachIn (toNTM (walkLeftK k s)) k (s, h, tp) (s + k, h - k, tp) := by
  induction k generalizing s h with
  | zero => exact rfl
  | succ k ih =>
      have run1 := moveLeft_run_eq s (s + 1) h tp hbound
      have run2 := ih (s + 1) (h - 1) (by omega)
      have comp := reachIn_seq (moveLeft s (s + 1)) (walkLeftK k (s + 1)) 1 k _ _ _ run1 run2
      convert comp using 1
      · omega
      · rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, by omega, rfl⟩

/-!
**The list-preserving left motions, proved.**  `moveLeft`/`walkLeftK` return the identical tape in bounds, completing
the list-preserving motion set (right by `walkRightK_run_eq`, left here).  Next: the compare-and-return loop body, the
unary-field equality comparison, and the rule-table scan-and-match — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq.moveLeft_run_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq.walkLeftK_run_eq

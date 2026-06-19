import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMMoveLeft

/-!
# Entry 355 — universal-TM-table build: the two-cell comparison `compareAdjacent` (proved)

The matching half so far (entries 351–353) compares the tape against *constant* patterns baked into the machine.  The
real rule match reads *both* operands from the tape.  This brick builds the first machine that **reads two tape cells
and compares them**: `compareAdjacent` reads cell `j`, carries its value in the control state (via `branchBit`),
advances, and checks whether cell `j+1` equals the carried value (via `checkBit`), routing to an equal-state on a match.

It is the conceptual core of the two-pointer comparison, assembled entirely from the now-complete primitive set
(`branchBit` carry, `scanBit` advance, `checkBit` compare), with the two control-flow arms (carried `true` / carried
`false`) living in one machine and lifted into it by the non-interference law `reachIn_append_left/right` (entry 347).

State layout from base `s`: `s` reads/branches, `s+1`/`s+2` carry `true`/`false`, `s+3`/`s+4` are post-advance on each
arm, `s+5` is the equal-state, `s+6` the not-equal state.

## What is proved (clean axioms, no `sorry`)

* **`compareAdjacent s`** — `branchBit s (s+1) (s+2) ++ ((scanBit (s+1) (s+3) ++ checkBit true (s+3) (s+5) (s+6)) ++
  (scanBit (s+2) (s+4) ++ checkBit false (s+4) (s+5) (s+6)))`.
* **`compareAdjacent_run_eq`** (PROVED) — if cells `j` and `j+1` are equal (`tp.getD j false = tp.getD (j+1) false`),
  then `∃ tp', reachIn (toNTM (compareAdjacent s)) 3 (s, j, tp) (s+5, j+2, tp')`: the comparison runs three steps to the
  equal-state `s+5`, head past both cells.

## Honest scope

This is the first **two-cell comparison reading both operands from the tape** — the carry-and-compare mechanism the
two-pointer key match generalises.  It proves the *equal ⇒ equal-state* direction for adjacent cells; it does **not**
yet prove the not-equal direction, nor generalise to two *distant* regions (where walking between them with
`scanBit`/`moveLeft` and a round-trip invariant is needed), nor the rule-table loop, nor the apply.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareAdjacent

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch (branchBit branchBit_run_true branchBit_run_false)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit scanBit_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit (checkBit checkBit_run_match)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left reachIn_append_right)

/-- **The two-cell comparison machine.**  Read cell `j` and carry its value (`branchBit`), advance (`scanBit`), check
cell `j+1` equals the carried value (`checkBit`); reach the equal-state `s+5` iff they agree. -/
def compareAdjacent (s : ℕ) : TMachine :=
  branchBit s (s + 1) (s + 2) ++
    ((scanBit (s + 1) (s + 3) ++ checkBit true (s + 3) (s + 5) (s + 6)) ++
     (scanBit (s + 2) (s + 4) ++ checkBit false (s + 4) (s + 5) (s + 6)))

/-- **The comparison reaches the equal-state on equal cells (PROVED).**  If cells `j` and `j+1` hold the same symbol,
`compareAdjacent s` runs three steps from `(s, j, tp)` to `(s+5, j+2, tp')`. -/
theorem compareAdjacent_run_eq (s j : ℕ) (tp : List Bool) (heq : tp.getD j false = tp.getD (j + 1) false) :
    ∃ tp', reachIn (toNTM (compareAdjacent s)) 3 (s, j, tp) (s + 5, j + 2, tp') := by
  by_cases hb : tp.getD j false = true
  · -- carried `true`
    have hjp1 : tp.getD (j + 1) false = true := by rw [← heq]; exact hb
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_true s (s + 1) (s + 2) j tp hb
    obtain ⟨tp2, run2, p2⟩ := scanBit_run_pres (s + 1) (s + 3) j tp1
    have ht3 : tp2.getD (j + 1) false = true := by rw [p2 (j + 1), p1 (j + 1)]; exact hjp1
    obtain ⟨tp3, run3, _⟩ := checkBit_run_match true (s + 3) (s + 5) (s + 6) (j + 1) tp2 ht3
    refine ⟨tp3, ?_⟩
    have arm := reachIn_seq (scanBit (s + 1) (s + 3)) (checkBit true (s + 3) (s + 5) (s + 6)) 1 1 _ _ _ run2 run3
    have ver := reachIn_append_left (scanBit (s + 1) (s + 3) ++ checkBit true (s + 3) (s + 5) (s + 6))
      (scanBit (s + 2) (s + 4) ++ checkBit false (s + 4) (s + 5) (s + 6)) 2 _ _ arm
    exact reachIn_seq (branchBit s (s + 1) (s + 2)) _ 1 2 _ _ _ run1 ver
  · -- carried `false`
    have hbf : tp.getD j false = false := by rw [Bool.not_eq_true] at hb; exact hb
    have hjp1 : tp.getD (j + 1) false = false := by rw [← heq]; exact hbf
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_false s (s + 1) (s + 2) j tp hbf
    obtain ⟨tp2, run2, p2⟩ := scanBit_run_pres (s + 2) (s + 4) j tp1
    have ht3 : tp2.getD (j + 1) false = false := by rw [p2 (j + 1), p1 (j + 1)]; exact hjp1
    obtain ⟨tp3, run3, _⟩ := checkBit_run_match false (s + 4) (s + 5) (s + 6) (j + 1) tp2 ht3
    refine ⟨tp3, ?_⟩
    have arm := reachIn_seq (scanBit (s + 2) (s + 4)) (checkBit false (s + 4) (s + 5) (s + 6)) 1 1 _ _ _ run2 run3
    have ver := reachIn_append_right (scanBit (s + 1) (s + 3) ++ checkBit true (s + 3) (s + 5) (s + 6))
      (scanBit (s + 2) (s + 4) ++ checkBit false (s + 4) (s + 5) (s + 6)) 2 _ _ arm
    exact reachIn_seq (branchBit s (s + 1) (s + 2)) _ 1 2 _ _ _ run1 ver

/-!
**The two-cell comparison, proved.**  `compareAdjacent` reads two tape cells, carries the first in the control state,
and routes to the equal-state when they agree — the carry-and-compare core of the two-pointer key match, with the two
arms unified by the non-interference law.  Next: the not-equal direction, the distant-region comparison (walking with
`scanBit`/`moveLeft` plus a round-trip invariant), the rule-table scan-and-match loop, and the apply — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareAdjacent

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareAdjacent.compareAdjacent_run_eq

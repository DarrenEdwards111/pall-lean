import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMWalkRightK

/-!
# Entry 358 — universal-TM-table build: the distant-region comparison `compareDistant` (proved)

`compareAdjacent` (entries 355–356) compares two *adjacent* cells.  The real key match compares cells in two *separated*
regions.  This brick generalises the carry-and-compare to an arbitrary gap `m`: read cell `j` and carry its value
(`branchBit`), walk right `m` cells to region B (`walkRightK`, on the carry track), then check cell `j+m` against the
carried value (`checkBit`), routing to an equal-state on a match.

This is the two-pointer comparison at full generality: a finite-control machine compares cell `j` with the distant cell
`j+m` by encoding cell `j` into the control state, traversing the gap on a per-value track, and comparing on arrival.
It is assembled entirely from the verified kinematic primitives (`branchBit`, `walkRightK`, `checkBit`), the two carry
tracks unified inside the one machine by the non-interference law.

## What is proved (clean axioms, no `sorry`)

* **`compareDistant m s sT0 sF0 E N`** — `branchBit s sT0 sF0 ++ ((walkRightK m sT0 ++ checkBit true (sT0+m) E N) ++
  (walkRightK m sF0 ++ checkBit false (sF0+m) E N))`: branch on cell `j`, walk `m` on the matching track, compare at
  `j+m`, reach `E` on a match (`N` on a mismatch).
* **`compareDistant_run_eq`** (PROVED) — if cells `j` and `j+m` agree (`tp.getD j false = tp.getD (j+m) false`), then
  `∃ tp', reachIn (toNTM (compareDistant m s sT0 sF0 E N)) (m+2) (s, j, tp) (E, j+m+1, tp')`: the comparison runs `m+2`
  steps to the equal-state `E`, head past region B.

## Honest scope

This is the **distant-region equality test** (equal ⇒ equal-state), the full-generality two-pointer comparison.  It does
**not** yet prove the not-equal direction at distance, nor the rule-table scan-and-match loop over the transition list,
nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistant

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch (branchBit branchBit_run_true branchBit_run_false)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit (checkBit checkBit_run_match)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkRightK (walkRightK walkRightK_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left reachIn_append_right)

/-- **The distant-region comparison machine.**  Branch on cell `j` (carry its value), walk `m` cells on the matching
track to region B, compare cell `j+m` against the carried value; reach the equal-state `E` iff they agree. -/
def compareDistant (m s sT0 sF0 E N : ℕ) : TMachine :=
  branchBit s sT0 sF0 ++
    ((walkRightK m sT0 ++ checkBit true (sT0 + m) E N) ++
     (walkRightK m sF0 ++ checkBit false (sF0 + m) E N))

/-- **The distant comparison reaches the equal-state on equal cells (PROVED).**  If cells `j` and `j+m` hold the same
symbol, `compareDistant m s sT0 sF0 E N` runs `m+2` steps from `(s, j, tp)` to `(E, j+m+1, tp')`. -/
theorem compareDistant_run_eq (m s sT0 sF0 E N j : ℕ) (tp : List Bool)
    (heq : tp.getD j false = tp.getD (j + m) false) :
    ∃ tp', reachIn (toNTM (compareDistant m s sT0 sF0 E N)) (m + 2) (s, j, tp) (E, j + m + 1, tp') := by
  by_cases hb : tp.getD j false = true
  · -- carried `true`
    have hjm : tp.getD (j + m) false = true := by rw [← heq]; exact hb
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_true s sT0 sF0 j tp hb
    obtain ⟨tp2, runW, pW⟩ := walkRightK_run m sT0 j tp1
    have ht : tp2.getD (j + m) false = true := by rw [pW (j + m), p1 (j + m)]; exact hjm
    obtain ⟨tp3, runC, _⟩ := checkBit_run_match true (sT0 + m) E N (j + m) tp2 ht
    refine ⟨tp3, ?_⟩
    have arm := reachIn_seq (walkRightK m sT0) (checkBit true (sT0 + m) E N) m 1 _ _ _ runW runC
    have ver := reachIn_append_left (walkRightK m sT0 ++ checkBit true (sT0 + m) E N)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) E N) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega
  · -- carried `false`
    have hbf : tp.getD j false = false := by rw [Bool.not_eq_true] at hb; exact hb
    have hjm : tp.getD (j + m) false = false := by rw [← heq]; exact hbf
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_false s sT0 sF0 j tp hbf
    obtain ⟨tp2, runW, pW⟩ := walkRightK_run m sF0 j tp1
    have ht : tp2.getD (j + m) false = false := by rw [pW (j + m), p1 (j + m)]; exact hjm
    obtain ⟨tp3, runC, _⟩ := checkBit_run_match false (sF0 + m) E N (j + m) tp2 ht
    refine ⟨tp3, ?_⟩
    have arm := reachIn_seq (walkRightK m sF0) (checkBit false (sF0 + m) E N) m 1 _ _ _ runW runC
    have ver := reachIn_append_right (walkRightK m sT0 ++ checkBit true (sT0 + m) E N)
      (walkRightK m sF0 ++ checkBit false (sF0 + m) E N) (m + 1) _ _ arm
    have full := reachIn_seq (branchBit s sT0 sF0) _ 1 (m + 1) _ _ _ run1 ver
    convert full using 1
    omega

/-!
**The distant-region comparison, proved.**  `compareDistant` compares cell `j` with the distant cell `j+m` by encoding
cell `j` into the control state, traversing the gap on a per-value track (`walkRightK`), and comparing on arrival
(`checkBit`) — the full-generality two-pointer match, the two tracks unified by the non-interference law.  Next: the
not-equal direction at distance, the rule-table scan-and-match loop, and the apply — fragment by verified fragment, not
faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistant

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistant.compareDistant_run_eq

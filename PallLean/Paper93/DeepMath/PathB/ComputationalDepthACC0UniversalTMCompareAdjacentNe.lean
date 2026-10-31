import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareAdjacent

/-!
# Entry 356 — universal-TM-table build: the not-equal branch of `compareAdjacent` (proved)

Entry 355 proved that `compareAdjacent s` reaches the equal-state `s+5` when the two cells agree.  This brick proves the
complementary direction: when the cells **differ**, the same machine reaches the not-equal state `s+6`.  Together with
entry 355 this makes `compareAdjacent` a *complete* two-cell equality decision — it routes to `s+5` exactly on a match
and to `s+6` exactly on a mismatch.

The proof mirrors `compareAdjacent_run_eq`: read cell `j` and carry it (`branchBit`), advance (`scanBit`), and on the
*mismatched* second cell take the failing `checkBit` branch (`checkBit_run_fail`) to `s+6` — the two arms again unified
inside the one machine by the non-interference law.

## What is proved (clean axioms, no `sorry`)

* **`compareAdjacent_run_ne`** (PROVED) — if cells `j` and `j+1` differ (`tp.getD j false ≠ tp.getD (j+1) false`), then
  `∃ tp', reachIn (toNTM (compareAdjacent s)) 3 (s, j, tp) (s+6, j+2, tp')`: the comparison runs three steps to the
  not-equal state `s+6`, head past both cells.

## Honest scope

This completes the **two-cell equality decision** (both the equal and not-equal outcomes for adjacent cells).  It does
**not** yet generalise to two *distant* regions (walking between them with a round-trip invariant), nor the rule-table
scan-and-match loop, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not
faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareAdjacentNe

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch (branchBit branchBit_run_true branchBit_run_false)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit scanBit_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit (checkBit checkBit_run_fail)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left reachIn_append_right)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareAdjacent (compareAdjacent)

/-- **The comparison reaches the not-equal state on differing cells (PROVED).**  If cells `j` and `j+1` hold different
symbols, `compareAdjacent s` runs three steps from `(s, j, tp)` to `(s+6, j+2, tp')`. -/
theorem compareAdjacent_run_ne (s j : ℕ) (tp : List Bool) (hne : tp.getD j false ≠ tp.getD (j + 1) false) :
    ∃ tp', reachIn (toNTM (compareAdjacent s)) 3 (s, j, tp) (s + 6, j + 2, tp') := by
  by_cases hb : tp.getD j false = true
  · -- carried `true`, so cell j+1 is `false`
    have hjp1 : tp.getD (j + 1) false = false := by
      have h2 : tp.getD (j + 1) false ≠ true := fun hc => hne (hb.trans hc.symm)
      simpa using h2
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_true s (s + 1) (s + 2) j tp hb
    obtain ⟨tp2, run2, p2⟩ := scanBit_run_pres (s + 1) (s + 3) j tp1
    have ht3 : tp2.getD (j + 1) false = !true := by
      rw [p2 (j + 1), p1 (j + 1), hjp1]; rfl
    obtain ⟨tp3, run3, _⟩ := checkBit_run_fail true (s + 3) (s + 5) (s + 6) (j + 1) tp2 ht3
    refine ⟨tp3, ?_⟩
    have arm := reachIn_seq (scanBit (s + 1) (s + 3)) (checkBit true (s + 3) (s + 5) (s + 6)) 1 1 _ _ _ run2 run3
    have ver := reachIn_append_left (scanBit (s + 1) (s + 3) ++ checkBit true (s + 3) (s + 5) (s + 6))
      (scanBit (s + 2) (s + 4) ++ checkBit false (s + 4) (s + 5) (s + 6)) 2 _ _ arm
    exact reachIn_seq (branchBit s (s + 1) (s + 2)) _ 1 2 _ _ _ run1 ver
  · -- carried `false`, so cell j+1 is `true`
    have hbf : tp.getD j false = false := by rw [Bool.not_eq_true] at hb; exact hb
    have hjp1 : tp.getD (j + 1) false = true := by
      have h2 : tp.getD (j + 1) false ≠ false := fun hc => hne (hbf.trans hc.symm)
      simpa using h2
    obtain ⟨tp1, run1, p1⟩ := branchBit_run_false s (s + 1) (s + 2) j tp hbf
    obtain ⟨tp2, run2, p2⟩ := scanBit_run_pres (s + 2) (s + 4) j tp1
    have ht3 : tp2.getD (j + 1) false = !false := by
      rw [p2 (j + 1), p1 (j + 1), hjp1]; rfl
    obtain ⟨tp3, run3, _⟩ := checkBit_run_fail false (s + 4) (s + 5) (s + 6) (j + 1) tp2 ht3
    refine ⟨tp3, ?_⟩
    have arm := reachIn_seq (scanBit (s + 2) (s + 4)) (checkBit false (s + 4) (s + 5) (s + 6)) 1 1 _ _ _ run2 run3
    have ver := reachIn_append_right (scanBit (s + 1) (s + 3) ++ checkBit true (s + 3) (s + 5) (s + 6))
      (scanBit (s + 2) (s + 4) ++ checkBit false (s + 4) (s + 5) (s + 6)) 2 _ _ arm
    exact reachIn_seq (branchBit s (s + 1) (s + 2)) _ 1 2 _ _ _ run1 ver

/-!
**The not-equal branch, proved.**  With `compareAdjacent_run_eq` (entry 355), `compareAdjacent` is now a complete
two-cell equality decision: `s+5` exactly on a match, `s+6` exactly on a mismatch.  Next: generalise to two distant
regions (walk between them with `scanBit`/`moveLeft` plus a round-trip invariant), then the rule-table scan-and-match
loop, then the apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareAdjacentNe

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareAdjacentNe.compareAdjacent_run_ne

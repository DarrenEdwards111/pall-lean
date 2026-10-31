import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMWalkLeftKEq

/-!
# Entry 377 — universal-TM-table build: the compare-and-return body `compareBitReturn` (proved)

Comparing two unary fields cell by cell needs a loop body that compares one pair, and *on a match* returns the head to
the next pair (and *on a mismatch* halts at the not-equal state).  `compareBitReturn` is the list-preserving distant
comparison (entry 375) with a `walkLeftK` return (entry 376) appended on the equal-state exit:

* on **equal** cells it reaches `E+m` at head `j+1` (the next source cell), tape identical — ready to loop;
* on **differing** cells it reaches `N` at head `j+m+1`, tape identical — the comparison aborts (the return walk, which
  starts at state `E`, is never entered).

## What is proved (clean axioms, no `sorry`)

* **`compareBitReturn m s sT0 sF0 E N`** — `compareDistant m s sT0 sF0 E N ++ walkLeftK m E`.
* **`compareBitReturn_run_eq`** (PROVED) — equal cells and `j+m+1 < tp.length` ⇒ `reachIn ... (2*m+2) (s, j, tp)
  (E+m, j+1, tp)`: match, head returned to the next pair, tape identical.
* **`compareBitReturn_run_ne`** (PROVED) — differing cells and `j+m < tp.length` ⇒ `reachIn ... (m+2) (s, j, tp)
  (N, j+m+1, tp)`: mismatch, halts at `N`, tape identical.

## Honest scope

This is the **compare-and-return body** — one iteration of a cell-by-cell field comparison.  It does **not** yet loop
over a field (the unary-field equality comparison, with its three-way continue/match/mismatch control flow), nor the
rule-table scan-and-match.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareBitReturn

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistant (compareDistant)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistantEq (compareDistant_run_eq compareDistant_run_ne)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq (walkLeftK_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left)

/-- **The compare-and-return body.**  Compare cell `j` with `j+m` (`compareDistant`); on the equal-state exit `E`, walk
`m` cells back left (`walkLeftK`) to the next source cell. -/
def compareBitReturn (m s sT0 sF0 E N : ℕ) : TMachine :=
  compareDistant m s sT0 sF0 E N ++ walkLeftK m E

/-- **The compare-and-return body on a match (PROVED).**  Equal cells: reaches `E+m` at head `j+1`, tape identical. -/
theorem compareBitReturn_run_eq (m s sT0 sF0 E N j : ℕ) (tp : List Bool)
    (heq : tp.getD j false = tp.getD (j + m) false) (hbound : j + m + 1 < tp.length) :
    reachIn (toNTM (compareBitReturn m s sT0 sF0 E N)) (2 * m + 2) (s, j, tp) (E + m, j + 1, tp) := by
  have run1 := compareDistant_run_eq m s sT0 sF0 E N j tp heq (by omega)
  have run2 := walkLeftK_run_eq m E (j + m + 1) tp (by omega)
  have comp := reachIn_seq (compareDistant m s sT0 sF0 E N) (walkLeftK m E) (m + 2) m _ _ _ run1 run2
  convert comp using 1
  · omega
  · rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨rfl, by omega, rfl⟩

/-- **The compare-and-return body on a mismatch (PROVED).**  Differing cells: halts at `N` at head `j+m+1`, tape
identical (the return walk, entered only at `E`, is never run). -/
theorem compareBitReturn_run_ne (m s sT0 sF0 E N j : ℕ) (tp : List Bool)
    (hne : tp.getD j false ≠ tp.getD (j + m) false) (hbound : j + m < tp.length) :
    reachIn (toNTM (compareBitReturn m s sT0 sF0 E N)) (m + 2) (s, j, tp) (N, j + m + 1, tp) := by
  have run1 := compareDistant_run_ne m s sT0 sF0 E N j tp hne hbound
  exact reachIn_append_left (compareDistant m s sT0 sF0 E N) (walkLeftK m E) (m + 2) _ _ run1

/-!
**The compare-and-return body, proved.**  `compareBitReturn` compares one cell pair and, on a match, returns the head
to the next pair (on a mismatch it halts at `N`) — the loop body of a cell-by-cell field comparison.  Next: loop it for
the unary-field equality comparison, then the rule-table scan-and-match — fragment by verified fragment, not faked.
Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareBitReturn

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareBitReturn.compareBitReturn_run_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareBitReturn.compareBitReturn_run_ne

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ScanTrans

/-!
# Entry 398 — universal-TM-table build: the 3-symbol rule-table scan `scanTable3` (proved)

The `Sym3` port of the rule-table scan (entry 372).  The list-preserving record scanner `scanTransFrom3_run_eq`
(entry 397) scans one transition leaving the marker tape identical; this brick **loops it over the whole transition
list**: `scanTable3 base Ms` scans the concatenation `Ms.flatMap encodeTransBits3` — the encoded rule table — from state
`base`, advancing the control state by `5` per transition, ending past the table.  Because the record scan is
list-preserving, the inductive step re-runs the scanner on the *same tape*, so the loop is a clean recursion.

## What is proved (clean axioms, no `sorry`)

* **`scanTable3 base Ms`** — recursively, `[] ↦ []` and `t :: ts ↦ scanTransFrom3 base ++ scanTable3 (base+5) ts`.
* **`scanTable3_run`** (PROVED) — `reachIn (toNTM3 (scanTable3 base Ms)) (Ms.flatMap encodeTransBits3).length
  (base, pre.length, pre ++ Ms.flatMap encodeTransBits3 ++ rest) (base + 5*Ms.length, pre.length + (Ms.flatMap
  encodeTransBits3).length, pre ++ Ms.flatMap encodeTransBits3 ++ rest)`: the table scan returns the *identical* tape,
  head past the whole encoded rule list.

## Honest scope

This is the **`Sym3` rule-table scan** — traversing the whole encoded transition list, list-preservingly.  It does
**not** yet *match* (compare each transition's key against the configuration), nor apply.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanTable

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans Move)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (encodeTransBits3 encodeTransBits3_length)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanTrans (scanTransFrom3 scanTransFrom3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The `Sym3` rule-table scan.**  Loop `scanTransFrom3` over the transition list, advancing the state by `5` per
transition. -/
def scanTable3 (base : ℕ) : List TMTrans → TMachine3
  | [] => []
  | _t :: ts => scanTransFrom3 base ++ scanTable3 (base + 5) ts

/-- **The `Sym3` rule-table scan run (PROVED).**  `scanTable3 base Ms` scans the whole encoded transition list
`Ms.flatMap encodeTransBits3` from state `base`, returning the *identical* tape, head past the table. -/
theorem scanTable3_run (base : ℕ) (Ms : List TMTrans) (pre rest : List Sym3) :
    reachIn (toNTM3 (scanTable3 base Ms)) (Ms.flatMap encodeTransBits3).length
      (base, pre.length, pre ++ Ms.flatMap encodeTransBits3 ++ rest)
      (base + 5 * Ms.length, pre.length + (Ms.flatMap encodeTransBits3).length,
        pre ++ Ms.flatMap encodeTransBits3 ++ rest) := by
  induction Ms generalizing base pre with
  | nil =>
      simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.add_zero, List.append_nil]
      rfl
  | cons t ts ih =>
      have run1 := scanTransFrom3_run_eq base t pre (ts.flatMap encodeTransBits3 ++ rest)
      simp only [← List.append_assoc] at run1
      have run2 := ih (base + 5) (pre ++ encodeTransBits3 t)
      rw [List.length_append, encodeTransBits3_length] at run2
      have comp := reachIn_seq3 _ _ _ _ _ _ _ run1 run2
      simp only [List.flatMap_cons, ← List.append_assoc, List.length_append, encodeTransBits3_length,
        List.length_cons]
      convert comp using 1
      rw [Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨by omega, by omega, rfl⟩

/-!
**The `Sym3` rule-table scan, proved.**  `scanTable3 base Ms` traverses the whole encoded transition list
list-preservingly, the loop a clean recursion over the list thanks to the list-preserving record scanner.  Next:
interleave the scan with a key comparison (the rule-table scan-and-match), then the apply — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanTable

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanTable.scanTable3_run

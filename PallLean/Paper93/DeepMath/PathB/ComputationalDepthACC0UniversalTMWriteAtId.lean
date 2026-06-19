import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanTransFromPres

/-!
# Entry 369 — universal-TM-table build: writing back within bounds is the identity (proved)

The scanners (`scanNatFrom`, `scanBit`, …) preserve the tape *content* (`getD` pointwise), which has sufficed so far.
But looping a scanner over the rule table needs the post-scan tape to equal the original **as a list** (so the
inductive step can re-run the scanner on it).  The foundation for that is: writing back the symbol a cell already holds
leaves the tape *exactly* unchanged, provided the position is in bounds.

`writeAt tape p w = (tape ++ replicate (p+1-tape.length) false).set p w`; when `p < tape.length` the padding is empty,
so `writeAt` is just `tape.set p w`, and writing back `tape.getD p false = tape[p]` is `tape.set p tape[p] = tape`.

## What is proved (clean axioms, no `sorry`)

* **`writeAt_id_of_lt`** (PROVED) — `p < tape.length → writeAt tape p (tape.getD p false) = tape`: a write-back at an
  in-bounds position is the identity *as a list* (not merely `getD`-equal).

## Honest scope

This is the **in-bounds write-back identity** — the foundation for list-level (not just content-level) scan
preservation, which the rule-table loop needs to re-run the scanner on the post-scan tape.  It does **not** itself
upgrade the scanners to list-preservation (that threads an in-bounds invariant through each step), nor build the table
loop, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteAtId

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (writeAt)

/-- **A write-back within bounds is the identity (PROVED).**  If `p < tape.length`, then writing back the symbol at `p`
leaves the tape exactly unchanged. -/
theorem writeAt_id_of_lt (tape : List Bool) (p : ℕ) (hp : p < tape.length) :
    writeAt tape p (tape.getD p false) = tape := by
  unfold writeAt
  rw [show p + 1 - tape.length = 0 from by omega, List.replicate_zero, List.append_nil,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some,
    List.set_getElem_self]

/-!
**The in-bounds write-back identity, proved.**  `writeAt_id_of_lt` upgrades "the scan preserves the content" toward
"the scan leaves the tape exactly unchanged" — the property the rule-table loop needs to re-run the scanner on the
post-scan tape.  Next: thread an in-bounds invariant through the scanners to get list-level preservation, then the
table loop, the scan-and-match, and the apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteAtId

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteAtId.writeAt_id_of_lt

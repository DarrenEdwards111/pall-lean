import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Unmark

/-!
# Entry 391 — universal-TM-table build: double-write `writeAt3_writeAt3` (proved)

The marker comparison anchors a cell with `M` (overwriting its `O`/`I`) and later restores it by writing the carried
value back.  Reasoning about that restore needs: writing twice at the *same* cell keeps only the last write.  In
particular, anchoring then restoring (`M` then the original value) collapses to a single write of the original value —
and if the original value is already there, it is the identity.

## What is proved (clean axioms, no `sorry`)

* **`writeAt3_writeAt3`** (PROVED) — `writeAt3 (writeAt3 tape p a) p b = writeAt3 tape p b`: a second write at the same
  position overrides the first.

## Honest scope

This is the **double-write collapse** — the algebraic fact the restore phase rests on.  It does **not** yet assemble the
shuttle-and-compare loop, nor the rule-table loop.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteWrite

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3)

/-- **A second write at the same position overrides the first (PROVED).** -/
theorem writeAt3_writeAt3 (tape : List Sym3) (p : ℕ) (a b : Sym3) :
    writeAt3 (writeAt3 tape p a) p b = writeAt3 tape p b := by
  unfold writeAt3
  rw [show p + 1 - ((tape ++ List.replicate (p + 1 - tape.length) Sym3.O).set p a).length = 0 from by
        simp only [List.length_set, List.length_append, List.length_replicate]; omega,
      List.replicate_zero, List.append_nil, List.set_set]

/-!
**Double-write collapse, proved.**  `writeAt3_writeAt3` lets the anchor-then-restore (write `M`, then the original
value) collapse to one write — the algebraic basis of the restore phase.  Next: assemble the shuttle-and-compare loop,
then the rule-table loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteWrite

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteWrite.writeAt3_writeAt3

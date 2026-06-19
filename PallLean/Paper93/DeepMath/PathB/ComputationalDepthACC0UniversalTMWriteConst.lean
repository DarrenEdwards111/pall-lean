import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareDistant

/-!
# Entry 359 — universal-TM-table build: the overwrite primitive `writeConst` (proved)

Every machine in the table build so far *writes back what it read* (scanners, checkers, comparators are all
tape-preserving).  The **apply** phase — rewriting the encoded configuration with the matched rule's right-hand side —
needs to *overwrite* a cell with a new value.  This brick adds the missing capability.

`writeConst b s s'` reads the current cell (whatever it is), **writes the constant `b`** in its place, moves right, and
transitions to `s'`.  Unlike `scanBit`/`checkBit`, it is *not* tape-preserving: it sets the head cell to `b`.  It is the
atom of the apply phase (writing the new state digit, the new symbol, etc.).

## What is proved (clean axioms, no `sorry`)

* **`writeConst b s s'`** — the machine `[((s,true),(s',b,→)), ((s,false),(s',b,→))]`: on either symbol, write `b`, move
  right, go to `s'`.
* **`writeConst_step`** (PROVED) — at `(s, j, tp)`, uniformly in the read symbol, it steps to `(s', j+1, writeAt tp j b)`
  — the head cell is overwritten with `b`.
* **`writeConst_run`** (PROVED) — `reachIn (toNTM (writeConst b s s')) 1 (s, h, tp) (s', h+1, writeAt tp h b)`: the
  one-step overwrite run, the head cell now holding `b`.

## Honest scope

This is the **overwrite atom** for the apply phase — the first machine that changes a tape cell rather than restoring
it.  It does **not** yet copy a value between regions (carry-and-write, the dual of `compareDistant`), nor assemble the
full apply (rewrite the configuration's state and symbol per the matched rule), nor the rule-table scan-and-match loop.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteConst

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine Move concreteStep readSym applyTrans moveHead writeAt toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)

/-- **The overwrite machine.**  At state `s`: read the cell, write the constant `b` in its place, move right, go to
`s'` — whatever the symbol read. -/
def writeConst (b : Bool) (s s' : ℕ) : TMachine :=
  [((s, true), (s', b, (1 : Move))), ((s, false), (s', b, (1 : Move)))]

/-- **`writeConst` overwrites the head cell (PROVED), uniformly in the read symbol.**  At `(s, j, tp)` it steps to
`(s', j+1, writeAt tp j b)` — the head cell now holds `b`. -/
theorem writeConst_step (b : Bool) (s s' j : ℕ) (tp : List Bool) :
    concreteStep (writeConst b s s') (s, j, tp) (s', j + 1, writeAt tp j b) := by
  cases h : tp.getD j false with
  | false =>
      refine ⟨((s, false), (s', b, (1 : Move))), ?_, ?_, ?_⟩
      · simp [writeConst]
      · show (s, false) = ((s, j, tp).1, readSym (s, j, tp))
        simp only [readSym, h]
      · simp [applyTrans, moveHead]
  | true =>
      refine ⟨((s, true), (s', b, (1 : Move))), ?_, ?_, ?_⟩
      · simp [writeConst]
      · show (s, true) = ((s, j, tp).1, readSym (s, j, tp))
        simp only [readSym, h]
      · simp [applyTrans, moveHead]

/-- **The one-step overwrite run (PROVED).**  From `(s, h, tp)`, `writeConst b s s'` reaches `(s', h+1, writeAt tp h b)`
in one step — the head cell now holds `b`. -/
theorem writeConst_run (b : Bool) (s s' h : ℕ) (tp : List Bool) :
    reachIn (toNTM (writeConst b s s')) 1 (s, h, tp) (s', h + 1, writeAt tp h b) :=
  ⟨_, writeConst_step b s s' h tp, rfl⟩

/-!
**The overwrite atom, proved.**  `writeConst b` is the first machine to change a tape cell — it sets the head cell to
the constant `b` and advances — the atom of the apply phase.  Next: carry-and-write (copy a value between regions, the
dual of `compareDistant`), the full apply (rewrite the configuration per the matched rule), and the rule-table loop —
fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteConst

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteConst.writeConst_step
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteConst.writeConst_run

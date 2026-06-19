import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMMatchPattern

/-!
# Entry 354 — universal-TM-table build: the leftward move `moveLeft` (proved)

Every machine in the table build so far moves the head *right* (`scanNatFrom`, `scanBit`, `checkBit`; move `1`) or
*stays* (`branchBit`; move `2`).  The two-pointer key comparison — the central remaining piece — needs the head to
travel **left**: after reading a bit in one tape region and walking to the other to compare, the head must return.  This
brick adds the missing direction.

`moveLeft s s'` reads the current cell, writes it back (non-destructive), moves the head **left** (move `0`, i.e.
`h ↦ h-1`), and transitions to `s'` — uniformly in the read symbol.  It is the leftward counterpart of `scanBit`.

## What is proved (clean axioms, no `sorry`)

* **`moveLeft s s'`** — the machine `[((s,true),(s',true,left)), ((s,false),(s',false,left))]`.
* **`moveLeft_step`** (PROVED) — at `(s, j, tp)`, uniformly in the read symbol, it steps to
  `(s', j-1, writeAt tp j (tp.getD j false))` — state `s'`, head moved left, symbol written back.
* **`moveLeft_run_pres`** (PROVED) — `∃ tp', reachIn (toNTM (moveLeft s s')) 1 (s, h, tp) (s', h-1, tp') ∧
  ∀ q, tp'.getD q false = tp.getD q false`: the one-step leftward run, preserving the tape.

## Honest scope

This adds the **leftward-movement atom** — the head direction the two-pointer comparison needs to return between tape
regions.  It does **not** yet assemble the two-region key comparison itself (read a bit in region A, carry it in the
control state, walk to region B, compare, return), nor the rule-table scan-and-match loop, nor the apply.  Building
those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMoveLeft

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine Move concreteStep readSym applyTrans moveHead writeAt toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD_self)

/-- **The leftward move machine.**  At state `s`: read the cell, write it back, move the head *left* (move `0`), and go
to `s'` — whatever the symbol. -/
def moveLeft (s s' : ℕ) : TMachine :=
  [((s, true), (s', true, (0 : Move))), ((s, false), (s', false, (0 : Move)))]

/-- **`moveLeft` moves the head left (PROVED), uniformly in the read symbol.**  At `(s, j, tp)`, it steps to
`(s', j-1, writeAt tp j (tp.getD j false))` — state `s'`, head one to the left, symbol written back. -/
theorem moveLeft_step (s s' j : ℕ) (tp : List Bool) :
    concreteStep (moveLeft s s') (s, j, tp) (s', j - 1, writeAt tp j (tp.getD j false)) := by
  cases h : tp.getD j false with
  | false =>
      refine ⟨((s, false), (s', false, (0 : Move))), ?_, ?_, ?_⟩
      · simp [moveLeft]
      · show (s, false) = ((s, j, tp).1, readSym (s, j, tp))
        simp only [readSym, h]
      · simp [applyTrans, moveHead]
  | true =>
      refine ⟨((s, true), (s', true, (0 : Move))), ?_, ?_, ?_⟩
      · simp [moveLeft]
      · show (s, true) = ((s, j, tp).1, readSym (s, j, tp))
        simp only [readSym, h]
      · simp [applyTrans, moveHead]

/-- **The one-step leftward run, preserving the tape (PROVED).**  From `(s, h, tp)`, `moveLeft` reaches `(s', h-1, tp')`
in one step, with `tp'` agreeing with `tp` on every cell. -/
theorem moveLeft_run_pres (s s' h : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (moveLeft s s')) 1 (s, h, tp) (s', h - 1, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  refine ⟨writeAt tp h (tp.getD h false), ⟨_, moveLeft_step s s' h tp, rfl⟩, ?_⟩
  intro q
  exact writeAt_getD_self tp h q

/-!
**The leftward move, proved.**  `moveLeft` is the first machine to travel left, completing the set of head motions
(right/stay/left) the universal table needs.  Next: assemble the two-region key comparison (carry a bit in the control
state, walk between regions using `scanBit`/`moveLeft`, compare), then the rule-table scan-and-match loop, then the
apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMoveLeft

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMoveLeft.moveLeft_step
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMoveLeft.moveLeft_run_pres

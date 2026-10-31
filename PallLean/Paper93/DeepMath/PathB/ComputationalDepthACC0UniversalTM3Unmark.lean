import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkCarry

/-!
# Entry 390 — universal-TM-table build: the restore primitive `unmark3` (proved)

The dual of `markCarry3` (entry 389): after the machine has anchored a cell with the marker `M`, carried its bit in the
control state, and shuttled away to compare, it must come back and **restore** the cell to its original value.
`unmark3 s s' w` overwrites the head cell with `w` (the carried value, chosen by which carry-track the machine is on)
and stays in place.

## What is proved (clean axioms, no `sorry`)

* **`unmark3 s s' w`** — `[((s,O),(s',w,stay)), ((s,I),(s',w,stay)), ((s,M),(s',w,stay))]`.
* **`unmark3_step`** (PROVED) — at `(s, j, tp)` writes `w`: steps to `(s', j, writeAt3 tp j w)`.
* **`unmark3_run`** (PROVED) — `reachIn (toNTM3 (unmark3 s s' w)) 1 (s, j, tp) (s', j, writeAt3 tp j w)`: the one-step
  restore (the caller supplies `w` = the carried bit).

## Honest scope

This is the **restore primitive** — writing the carried value back over the marker.  It does **not** yet assemble the
shuttle-and-compare loop, nor the rule-table loop.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3)

/-- **The restore machine.**  At state `s`, on any symbol, write `w`, *stay*, go to `s'`. -/
def unmark3 (s s' : ℕ) (w : Sym3) : TMachine3 :=
  [((s, Sym3.O), (s', w, (2 : Move))), ((s, Sym3.I), (s', w, (2 : Move))),
   ((s, Sym3.M), (s', w, (2 : Move)))]

/-- **`unmark3` writes `w` (PROVED), uniformly in the read symbol.** -/
theorem unmark3_step (s s' : ℕ) (w : Sym3) (j : ℕ) (tp : List Sym3) :
    concreteStep3 (unmark3 s s' w) (s, j, tp) (s', j, writeAt3 tp j w) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · exact ⟨((s, Sym3.O), (s', w, (2 : Move))), by simp [unmark3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.I), (s', w, (2 : Move))), by simp [unmark3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.M), (s', w, (2 : Move))), by simp [unmark3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-- **The one-step restore (PROVED).** -/
theorem unmark3_run (s s' : ℕ) (w : Sym3) (j : ℕ) (tp : List Sym3) :
    reachIn (toNTM3 (unmark3 s s' w)) 1 (s, j, tp) (s', j, writeAt3 tp j w) :=
  ⟨_, unmark3_step s s' w j tp, rfl⟩

/-!
**The restore primitive, proved.**  `unmark3` writes the carried value back over the marker, completing the
mark / carry / shuttle / compare / restore cycle's restore phase.  Next: assemble the shuttle-and-compare loop, then the
rule-table loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark.unmark3_run

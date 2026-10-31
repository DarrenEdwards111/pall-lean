import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR

/-!
# Entry 389 — universal-TM-table build: anchor-and-carry `markCarry3` (proved)

The marker comparison starts each cell-pair by *anchoring* one operand: read the cell's bit, **remember its value in the
control state**, and overwrite the cell with the marker `M`.  The machine can then shuttle to the other operand and
later seek back to this `M` (the anchor), comparing the carried bit — all distance-independent.

`markCarry3 s sO sI sM` reads the head cell and, *staying in place*, writes `M` and goes to `sO` (if the cell was `O`),
`sI` (if `I`), or `sM` (if already `M`).  The original `O`/`I` value is preserved in the control state for the later
comparison and restore.

## What is proved (clean axioms, no `sorry`)

* **`markCarry3 s sO sI sM`** — `[((s,O),(sO,M,stay)), ((s,I),(sI,M,stay)), ((s,M),(sM,M,stay))]`.
* **`markCarry3_run_O`** (PROVED) — cell is `O` ⇒ `reachIn (toNTM3 (markCarry3 s sO sI sM)) 1 (s, j, tp) (sO, j,
  writeAt3 tp j M)`: anchor laid, value `O` remembered in `sO`.
* **`markCarry3_run_I`** (PROVED) — cell is `I` ⇒ reaches `(sI, j, writeAt3 tp j M)`.

## Honest scope

This is the **anchor-and-carry** step — the start of one cell-pair comparison.  It does **not** yet shuttle to the other
operand, compare, restore, or loop.  Building those fragment by fragment is the genuine remaining construction, **not
faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkCarry

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3)

/-- **The anchor-and-carry machine.**  Read the head cell, write the marker `M`, *stay*, and branch the control state
on the original value: `sO` if it was `O`, `sI` if `I`, `sM` if already `M`. -/
def markCarry3 (s sO sI sM : ℕ) : TMachine3 :=
  [((s, Sym3.O), (sO, Sym3.M, (2 : Move))), ((s, Sym3.I), (sI, Sym3.M, (2 : Move))),
   ((s, Sym3.M), (sM, Sym3.M, (2 : Move)))]

/-- **Anchor-and-carry on `O` (PROVED).** -/
theorem markCarry3_run_O (s sO sI sM j : ℕ) (tp : List Sym3) (h : readSym3 (s, j, tp) = Sym3.O) :
    reachIn (toNTM3 (markCarry3 s sO sI sM)) 1 (s, j, tp) (sO, j, writeAt3 tp j Sym3.M) := by
  refine ⟨(sO, j, writeAt3 tp j Sym3.M), ?_, rfl⟩
  exact ⟨((s, Sym3.O), (sO, Sym3.M, (2 : Move))), by simp [markCarry3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-- **Anchor-and-carry on `I` (PROVED).** -/
theorem markCarry3_run_I (s sO sI sM j : ℕ) (tp : List Sym3) (h : readSym3 (s, j, tp) = Sym3.I) :
    reachIn (toNTM3 (markCarry3 s sO sI sM)) 1 (s, j, tp) (sI, j, writeAt3 tp j Sym3.M) := by
  refine ⟨(sI, j, writeAt3 tp j Sym3.M), ?_, rfl⟩
  exact ⟨((s, Sym3.I), (sI, Sym3.M, (2 : Move))), by simp [markCarry3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-!
**Anchor-and-carry, proved.**  `markCarry3` lays the marker `M` at the head and remembers the original bit in the
control state — the start of a distance-independent cell-pair comparison.  Next: shuttle to the other operand, compare,
and restore — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkCarry

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkCarry.markCarry3_run_O
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkCarry.markCarry3_run_I

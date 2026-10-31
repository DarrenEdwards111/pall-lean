import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Move

/-!
# Entry 472 — generic scan loop: the cursor-advance `markAdvance3` (proved)

The core operation of the comparison shuttle the generic scan loop needs (per the fixed-`U` finding, entry 467): a
**cursor** is a marker `M` placed on a cell of a unary field; advancing it means restoring the marked cell to `I` and
moving the marker one cell right — *detecting whether the field continues* (the next cell is `I`) or *ends* (the next cell
is the separator `O`).  This is the tape-preserving step that lets a fixed machine walk a unary field with a movable cursor.

`markAdvance3 s smid sCont sEnd` is the 3-rule machine: at the cursor `M`, restore `I` and move right; then on `I` re-mark
(cursor advanced, `→ sCont`), or on `O` stop (field ended, `→ sEnd`).

## What is proved (clean axioms, no `sorry`)

* **`markAdvance3 s smid sCont sEnd`** — the cursor-advance machine.
* **`markAdvance3_run_cont`** (PROVED) — cursor at `j` (`tp[j]=M`), next cell `I`: in 2 steps reaches `(sCont, j+1,
  writeAt3 (writeAt3 tp j I) (j+1) M)` — cursor moved from `j` to `j+1`, the old cell restored to `I`.
* **`markAdvance3_run_end`** (PROVED) — cursor at `j`, next cell `O`: in 2 steps reaches `(sEnd, j+1, writeAt3 (writeAt3 tp
  j I) (j+1) O)` — cursor removed (old cell restored to `I`), head on the separator.

## Honest scope

This is the **cursor-advance** operation of the comparison shuttle.  It does **not** yet build the full two-field
comparison, the match-or-advance branch, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3 writeAt3_getD)

/-- **The cursor-advance machine.**  At the cursor `M`, restore `I` and move right; then on `I` re-mark (`→ sCont`), or on
the separator `O` stop (`→ sEnd`). -/
def markAdvance3 (s smid sCont sEnd : ℕ) : TMachine3 :=
  [((s, Sym3.M), (smid, Sym3.I, (1 : Move))),
   ((smid, Sym3.I), (sCont, Sym3.M, (2 : Move))),
   ((smid, Sym3.O), (sEnd, Sym3.O, (2 : Move)))]

/-- **Cursor advances within the field (PROVED).** -/
theorem markAdvance3_run_cont (s smid sCont sEnd j : ℕ) (tp : List Sym3)
    (hM : tp.getD j Sym3.O = Sym3.M) (hI : tp.getD (j + 1) Sym3.O = Sym3.I) :
    reachIn (toNTM3 (markAdvance3 s smid sCont sEnd)) 2 (s, j, tp)
      (sCont, j + 1, writeAt3 (writeAt3 tp j Sym3.I) (j + 1) Sym3.M) := by
  have hMr : readSym3 (s, j, tp) = Sym3.M := hM
  have step1 : concreteStep3 (markAdvance3 s smid sCont sEnd) (s, j, tp) (smid, j + 1, writeAt3 tp j Sym3.I) :=
    ⟨((s, Sym3.M), (smid, Sym3.I, (1 : Move))), by simp [markAdvance3], by simp [hMr],
     by simp [applyTrans3, moveHead]⟩
  have hI' : readSym3 (smid, j + 1, writeAt3 tp j Sym3.I) = Sym3.I := by
    show (writeAt3 tp j Sym3.I).getD (j + 1) Sym3.O = Sym3.I
    rw [writeAt3_getD]; split
    · rfl
    · exact hI
  have step2 : concreteStep3 (markAdvance3 s smid sCont sEnd) (smid, j + 1, writeAt3 tp j Sym3.I)
      (sCont, j + 1, writeAt3 (writeAt3 tp j Sym3.I) (j + 1) Sym3.M) :=
    ⟨((smid, Sym3.I), (sCont, Sym3.M, (2 : Move))), by simp [markAdvance3], by simp [hI'],
     by simp [applyTrans3, moveHead]⟩
  exact (reachIn_add (toNTM3 (markAdvance3 s smid sCont sEnd)) 1 1 _ _).mpr
    ⟨_, ⟨_, step1, rfl⟩, ⟨_, step2, rfl⟩⟩

/-- **Cursor reaches the field end (PROVED).** -/
theorem markAdvance3_run_end (s smid sCont sEnd j : ℕ) (tp : List Sym3)
    (hM : tp.getD j Sym3.O = Sym3.M) (hO : tp.getD (j + 1) Sym3.O = Sym3.O) :
    reachIn (toNTM3 (markAdvance3 s smid sCont sEnd)) 2 (s, j, tp)
      (sEnd, j + 1, writeAt3 (writeAt3 tp j Sym3.I) (j + 1) Sym3.O) := by
  have hMr : readSym3 (s, j, tp) = Sym3.M := hM
  have step1 : concreteStep3 (markAdvance3 s smid sCont sEnd) (s, j, tp) (smid, j + 1, writeAt3 tp j Sym3.I) :=
    ⟨((s, Sym3.M), (smid, Sym3.I, (1 : Move))), by simp [markAdvance3], by simp [hMr],
     by simp [applyTrans3, moveHead]⟩
  have hO' : readSym3 (smid, j + 1, writeAt3 tp j Sym3.I) = Sym3.O := by
    show (writeAt3 tp j Sym3.I).getD (j + 1) Sym3.O = Sym3.O
    rw [writeAt3_getD]; split
    · next h => omega
    · exact hO
  have step2 : concreteStep3 (markAdvance3 s smid sCont sEnd) (smid, j + 1, writeAt3 tp j Sym3.I)
      (sEnd, j + 1, writeAt3 (writeAt3 tp j Sym3.I) (j + 1) Sym3.O) :=
    ⟨((smid, Sym3.O), (sEnd, Sym3.O, (2 : Move))), by simp [markAdvance3], by simp [hO'],
     by simp [applyTrans3, moveHead]⟩
  exact (reachIn_add (toNTM3 (markAdvance3 s smid sCont sEnd)) 1 1 _ _).mpr
    ⟨_, ⟨_, step1, rfl⟩, ⟨_, step2, rfl⟩⟩

/-!
**The cursor-advance, proved.**  `markAdvance3` advances a unary-field cursor one cell, restoring the old cell and detecting
the field end — the tape-preserving step of the comparison shuttle.  Next: the two-field comparison loop, the
match-or-advance branch, the generic apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance.markAdvance3_run_cont
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance.markAdvance3_run_end

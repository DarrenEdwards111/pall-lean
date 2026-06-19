import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Compose

/-!
# Entry 385 — universal-TM-table build: marker write and 3-symbol right move (proved)

The first marker-track primitives over the 3-symbol model (entry 383): writing the marker `M` (the returnable anchor of
the varying-distance comparison) and a tape-preserving rightward move (the shuttle step).

* **`writeMark3 s s'`** overwrites the head cell with the marker `M` and moves right.
* **`moveRight3 s s'`** reads the cell, writes it back, and moves right — list-preserving in bounds (`writeAt3_id_of_lt`,
  entry 383), the Sym3 analog of `scanBit`.

## What is proved (clean axioms, no `sorry`)

* **`writeMark3_step`** (PROVED) — at `(s, j, tp)` writes `M`: steps to `(s', j+1, writeAt3 tp j M)`.
* **`writeMark3_run`** (PROVED) — the one-step marker write: `reachIn (toNTM3 (writeMark3 s s')) 1 (s, j, tp)
  (s', j+1, writeAt3 tp j M)`.
* **`moveRight3_step`** (PROVED) — at `(s, j, tp)` steps to `(s', j+1, writeAt3 tp j (readSym3 (s,j,tp)))`.
* **`moveRight3_run_eq`** (PROVED) — `j < tp.length → reachIn (toNTM3 (moveRight3 s s')) 1 (s, j, tp) (s', j+1, tp)`:
  one rightward step leaving the tape *identical*.

## Honest scope

These are the **marker write and the 3-symbol right move** — the first marker-track primitives.  They do **not** yet
assemble the marker-based comparison, nor the rule-table loop.  Building those fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3 writeAt3_id_of_lt)

/-- **The marker-write machine.**  At state `s`, on any symbol, write the marker `M`, move right, go to `s'`. -/
def writeMark3 (s s' : ℕ) : TMachine3 :=
  [((s, Sym3.O), (s', Sym3.M, (1 : Move))), ((s, Sym3.I), (s', Sym3.M, (1 : Move))),
   ((s, Sym3.M), (s', Sym3.M, (1 : Move)))]

/-- **`writeMark3` writes `M` (PROVED), uniformly in the read symbol.** -/
theorem writeMark3_step (s s' j : ℕ) (tp : List Sym3) :
    concreteStep3 (writeMark3 s s') (s, j, tp) (s', j + 1, writeAt3 tp j Sym3.M) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · exact ⟨((s, Sym3.O), (s', Sym3.M, (1 : Move))), by simp [writeMark3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.I), (s', Sym3.M, (1 : Move))), by simp [writeMark3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.M), (s', Sym3.M, (1 : Move))), by simp [writeMark3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-- **The one-step marker write (PROVED).** -/
theorem writeMark3_run (s s' j : ℕ) (tp : List Sym3) :
    reachIn (toNTM3 (writeMark3 s s')) 1 (s, j, tp) (s', j + 1, writeAt3 tp j Sym3.M) :=
  ⟨_, writeMark3_step s s' j tp, rfl⟩

/-- **The tape-preserving right move machine.**  At state `s`, on any symbol, write it back, move right, go to `s'`. -/
def moveRight3 (s s' : ℕ) : TMachine3 :=
  [((s, Sym3.O), (s', Sym3.O, (1 : Move))), ((s, Sym3.I), (s', Sym3.I, (1 : Move))),
   ((s, Sym3.M), (s', Sym3.M, (1 : Move)))]

/-- **`moveRight3` writes back the read symbol (PROVED).** -/
theorem moveRight3_step (s s' j : ℕ) (tp : List Sym3) :
    concreteStep3 (moveRight3 s s') (s, j, tp) (s', j + 1, writeAt3 tp j (readSym3 (s, j, tp))) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · exact ⟨((s, Sym3.O), (s', Sym3.O, (1 : Move))), by simp [moveRight3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.I), (s', Sym3.I, (1 : Move))), by simp [moveRight3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.M), (s', Sym3.M, (1 : Move))), by simp [moveRight3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-- **The tape-preserving right move (PROVED).**  `j < tp.length → reachIn (toNTM3 (moveRight3 s s')) 1 (s, j, tp)
(s', j+1, tp)`: one rightward step leaving the tape identical. -/
theorem moveRight3_run_eq (s s' j : ℕ) (tp : List Sym3) (hbound : j < tp.length) :
    reachIn (toNTM3 (moveRight3 s s')) 1 (s, j, tp) (s', j + 1, tp) := by
  have hstep := moveRight3_step s s' j tp
  rw [show readSym3 (s, j, tp) = tp.getD j Sym3.O from rfl, writeAt3_id_of_lt tp j hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-!
**Marker write and 3-symbol right move, proved.**  `writeMark3` lays the marker anchor and `moveRight3` shuttles right
preserving the tape — the first marker-track primitives.  Next: a leftward move and a seek-to-marker, then the
marker-based varying-distance comparison — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move.writeMark3_run
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move.moveRight3_run_eq

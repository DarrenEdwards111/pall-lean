import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Move

/-!
# Entry 386 — universal-TM-table build: left move and branch-on-marker (proved)

Two more marker-track primitives: a tape-preserving leftward shuttle (`moveLeft3`) and a **branch on the marker**
(`branchMark3`) — the latter is what makes the varying distance irrelevant: a seek loop reads the cell, and `branchMark3`
routes to "found" if it is the marker `M` or "keep going" otherwise, so the head finds the anchor regardless of how far
it is.

## What is proved (clean axioms, no `sorry`)

* **`moveLeft3 s s'`** — write back the read symbol, move left.  **`moveLeft3_run_eq`** (PROVED) — `j < tp.length →
  reachIn (toNTM3 (moveLeft3 s s')) 1 (s, j, tp) (s', j-1, tp)`, tape identical.
* **`branchMark3 s sFound sCont`** — at the head, *stay*; go to `sFound` if the cell is `M`, else to `sCont`.
  **`branchMark3_run_mark`** (PROVED) — `readSym3 = M` and in bounds ⇒ reaches `(sFound, j, tp)`.
  **`branchMark3_run_notmark`** (PROVED) — `readSym3 ≠ M` and in bounds ⇒ reaches `(sCont, j, tp)`.  Both tape identical.

## Honest scope

These add the **left shuttle and the marker branch** — the components of a seek-to-marker loop.  They do **not** yet
build the seek loop, nor the marker comparison, nor the rule-table loop.  Building those fragment by fragment is the
genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3 writeAt3_id_of_lt)

/-- **The tape-preserving left move machine.** -/
def moveLeft3 (s s' : ℕ) : TMachine3 :=
  [((s, Sym3.O), (s', Sym3.O, (0 : Move))), ((s, Sym3.I), (s', Sym3.I, (0 : Move))),
   ((s, Sym3.M), (s', Sym3.M, (0 : Move)))]

theorem moveLeft3_step (s s' j : ℕ) (tp : List Sym3) :
    concreteStep3 (moveLeft3 s s') (s, j, tp) (s', j - 1, writeAt3 tp j (readSym3 (s, j, tp))) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · exact ⟨((s, Sym3.O), (s', Sym3.O, (0 : Move))), by simp [moveLeft3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.I), (s', Sym3.I, (0 : Move))), by simp [moveLeft3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.M), (s', Sym3.M, (0 : Move))), by simp [moveLeft3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-- **The tape-preserving left move (PROVED).** -/
theorem moveLeft3_run_eq (s s' j : ℕ) (tp : List Sym3) (hbound : j < tp.length) :
    reachIn (toNTM3 (moveLeft3 s s')) 1 (s, j, tp) (s', j - 1, tp) := by
  have hstep := moveLeft3_step s s' j tp
  rw [show readSym3 (s, j, tp) = tp.getD j Sym3.O from rfl, writeAt3_id_of_lt tp j hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-- **The branch-on-marker machine.**  At the head, *stay*; go to `sFound` if the cell is `M`, else to `sCont`. -/
def branchMark3 (s sFound sCont : ℕ) : TMachine3 :=
  [((s, Sym3.M), (sFound, Sym3.M, (2 : Move))), ((s, Sym3.O), (sCont, Sym3.O, (2 : Move))),
   ((s, Sym3.I), (sCont, Sym3.I, (2 : Move)))]

/-- **`branchMark3` on the marker (PROVED).** -/
theorem branchMark3_run_mark (s sFound sCont j : ℕ) (tp : List Sym3)
    (h : readSym3 (s, j, tp) = Sym3.M) (hbound : j < tp.length) :
    reachIn (toNTM3 (branchMark3 s sFound sCont)) 1 (s, j, tp) (sFound, j, tp) := by
  refine ⟨(sFound, j, tp), ?_, rfl⟩
  have hstep : concreteStep3 (branchMark3 s sFound sCont) (s, j, tp) (sFound, j, writeAt3 tp j Sym3.M) :=
    ⟨((s, Sym3.M), (sFound, Sym3.M, (2 : Move))), by simp [branchMark3], by simp [h], by simp [applyTrans3, moveHead]⟩
  rwa [show writeAt3 tp j Sym3.M = tp from by rw [← h]; exact writeAt3_id_of_lt tp j hbound] at hstep

/-- **`branchMark3` off the marker (PROVED).** -/
theorem branchMark3_run_notmark (s sFound sCont j : ℕ) (tp : List Sym3)
    (hne : readSym3 (s, j, tp) ≠ Sym3.M) (hbound : j < tp.length) :
    reachIn (toNTM3 (branchMark3 s sFound sCont)) 1 (s, j, tp) (sCont, j, tp) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · refine ⟨(sCont, j, tp), ?_, rfl⟩
    have hstep : concreteStep3 (branchMark3 s sFound sCont) (s, j, tp) (sCont, j, writeAt3 tp j Sym3.O) :=
      ⟨((s, Sym3.O), (sCont, Sym3.O, (2 : Move))), by simp [branchMark3], by simp [h], by simp [applyTrans3, moveHead]⟩
    rwa [show writeAt3 tp j Sym3.O = tp from by rw [← h]; exact writeAt3_id_of_lt tp j hbound] at hstep
  · refine ⟨(sCont, j, tp), ?_, rfl⟩
    have hstep : concreteStep3 (branchMark3 s sFound sCont) (s, j, tp) (sCont, j, writeAt3 tp j Sym3.I) :=
      ⟨((s, Sym3.I), (sCont, Sym3.I, (2 : Move))), by simp [branchMark3], by simp [h], by simp [applyTrans3, moveHead]⟩
    rwa [show writeAt3 tp j Sym3.I = tp from by rw [← h]; exact writeAt3_id_of_lt tp j hbound] at hstep
  · exact absurd h hne

/-!
**Left shuttle and marker branch, proved.**  `moveLeft3` shuttles left preserving the tape, and `branchMark3` routes on
whether the head cell is the marker — the heart of a distance-agnostic seek.  Next: the seek-to-marker loop, then the
marker-based comparison — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark.moveLeft3_run_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark.branchMark3_run_mark
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark.branchMark3_run_notmark

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Compose

/-!
# Entry 418 — universal-TM-table build: the counter-driven walk `walkRightClearField3` (proved)

The explicit unary head-pointer layout needs **data-dependent addressing**: to refresh the cached symbol the universal
machine must move the head right by an amount given by a unary count.  This brick is that data-dependent rightward walk —
a *counter-driven* loop that consumes a unary tally: read the cell, on a one (`I`) clear it to `O` and step right, on the
separator (`O`) stop.  It walks the head right by the tally's length (a data-determined distance), leaving the tally
cleared and the head at the separator.

Unlike `scanNatFrom3` (which walks a field non-destructively to its end), this *consumes* the tally — the form needed when
the count drives a separate motion and must be ticked off.

## What is proved (clean axioms, no `sorry`)

* **`walkStep3 s sCont sDone`** / **`walkStep3_run_I` / `_O`** (PROVED) — one cell: on `I`, clear to `O`, move right, go
  `sCont`; on `O` (separator), stay, go `sDone`.
* **`clearBlock tp h m`** — `tp` with cells `h … h+m-1` cleared to `O` (fold in loop order).
* **`walkRightClearField3 s sDone L`** / **`walkRightClearField3_run`** (PROVED) — for a unary tally (`m` ones then `O` at
  `h`), `m < L`, `h+m < tp.length`: `∃ N, reachIn N (s, h, tp) (sDone, h+m, clearBlock tp h m)` — head moves right by `m`,
  the tally cleared.

## Honest scope

This is the **counter-driven data-dependent walk** — the first genuine piece of unary-pointer addressing.  It does **not**
yet assemble the cache refresh (which must relate the head-pointer count to the tape offset), nor `apply3`.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 toNTM3 writeAt3 applyTrans3 writeAt3_getD writeAt3_id_of_lt)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_seq3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The counter-walk step.**  On `I`: clear to `O`, move right, go `sCont`.  On `O` (separator): stay, go `sDone`. -/
def walkStep3 (s sCont sDone : ℕ) : TMachine3 :=
  [((s, Sym3.I), (sCont, Sym3.O, (1 : Move))), ((s, Sym3.O), (sDone, Sym3.O, (2 : Move))),
   ((s, Sym3.M), (sDone, Sym3.M, (2 : Move)))]

/-- **The counter-walk step on `I` (PROVED).**  Clear the cell, move right. -/
theorem walkStep3_run_I (s sCont sDone j : ℕ) (tp : List Sym3) (h : tp.getD j Sym3.O = Sym3.I) :
    reachIn (toNTM3 (walkStep3 s sCont sDone)) 1 (s, j, tp) (sCont, j + 1, writeAt3 tp j Sym3.O) := by
  refine ⟨(sCont, j + 1, writeAt3 tp j Sym3.O), ?_, rfl⟩
  refine ⟨((s, Sym3.I), (sCont, Sym3.O, (1 : Move))), by simp [walkStep3], ?_, ?_⟩
  · show (s, Sym3.I) = ((s, j, tp).1, readSym3 (s, j, tp)); simp only [readSym3, h]
  · simp [applyTrans3, moveHead]

/-- **The counter-walk step on `O` (PROVED).**  Stay, tape identical, go `sDone`. -/
theorem walkStep3_run_O (s sCont sDone j : ℕ) (tp : List Sym3) (h : tp.getD j Sym3.O = Sym3.O)
    (hj : j < tp.length) :
    reachIn (toNTM3 (walkStep3 s sCont sDone)) 1 (s, j, tp) (sDone, j, tp) := by
  have hw : writeAt3 tp j Sym3.O = tp := h ▸ writeAt3_id_of_lt tp j hj
  refine ⟨(sDone, j, tp), ?_, rfl⟩
  refine ⟨((s, Sym3.O), (sDone, Sym3.O, (2 : Move))), by simp [walkStep3], ?_, ?_⟩
  · show (s, Sym3.O) = ((s, j, tp).1, readSym3 (s, j, tp)); simp only [readSym3, h]
  · simp [applyTrans3, moveHead, hw]

/-- **The cleared tape**, defined in the loop's order: clear cell `h`, then recurse on `h+1`. -/
def clearBlock (tp : List Sym3) (h : ℕ) : ℕ → List Sym3
  | 0 => tp
  | (m + 1) => clearBlock (writeAt3 tp h Sym3.O) (h + 1) m

/-- **The counter-driven rightward walk.**  Each iteration: one counter-walk step (continue ↦ next state), then recurse. -/
def walkRightClearField3 (s sDone : ℕ) : ℕ → TMachine3
  | 0 => []
  | (L + 1) => walkStep3 s (s + 1) sDone ++ walkRightClearField3 (s + 1) sDone L

/-- **The counter-driven walk run (PROVED).**  Walks the head right by the tally length `m`, clearing the tally; head ends
at `h+m`. -/
theorem walkRightClearField3_run (sDone : ℕ) :
    ∀ (L s h m : ℕ) (tp : List Sym3), m < L → h + m < tp.length →
      (∀ i, i < m → tp.getD (h + i) Sym3.O = Sym3.I) → tp.getD (h + m) Sym3.O = Sym3.O →
      ∃ N, reachIn (toNTM3 (walkRightClearField3 s sDone L)) N (s, h, tp) (sDone, h + m, clearBlock tp h m) := by
  intro L
  induction L with
  | zero => intro s h m tp hmL _ _ _; exact absurd hmL (Nat.not_lt_zero _)
  | succ L ih =>
    intro s h m tp hmL hbnd hco hcs
    cases m with
    | zero =>
        have hc0 : tp.getD h Sym3.O = Sym3.O := by have := hcs; rwa [Nat.add_zero] at this
        have hstep := walkStep3_run_O s (s + 1) sDone h tp hc0 (by omega)
        exact ⟨1, reachIn_append_left3 (walkStep3 s (s + 1) sDone) (walkRightClearField3 (s + 1) sDone L) 1 _ _ hstep⟩
    | succ m' =>
        have hcI : tp.getD h Sym3.O = Sym3.I := by have := hco 0 (by omega); rwa [Nat.add_zero] at this
        have hstep := walkStep3_run_I s (s + 1) sDone h tp hcI
        have hlen1 : (writeAt3 tp h Sym3.O).length = tp.length := writeAt3_length_eq tp h Sym3.O (by omega)
        obtain ⟨N3, hrec⟩ := ih (s + 1) (h + 1) m' (writeAt3 tp h Sym3.O) (by omega) (by rw [hlen1]; omega)
          (fun i hi => by
            rw [writeAt3_getD, if_neg (by omega), show h + 1 + i = h + (i + 1) from by omega]
            exact hco (i + 1) (by omega))
          (by rw [writeAt3_getD, if_neg (by omega), show h + 1 + m' = h + (m' + 1) from by omega]; exact hcs)
        rw [show h + 1 + m' = h + (m' + 1) from by omega] at hrec
        exact ⟨1 + N3, reachIn_seq3 (walkStep3 s (s + 1) sDone) (walkRightClearField3 (s + 1) sDone L)
          1 N3 _ _ _ hstep hrec⟩

/-!
**The counter-driven walk, proved.**  `walkRightClearField3` moves the head right by a data-determined amount given by a
unary tally, consuming it — the first genuine piece of unary head-pointer addressing.  Next: relate the head-pointer count
to the tape offset to refresh the cached symbol, and assemble `apply3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk.walkRightClearField3_run

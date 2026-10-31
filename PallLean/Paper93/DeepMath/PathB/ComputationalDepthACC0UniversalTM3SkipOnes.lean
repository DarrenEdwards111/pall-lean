import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR

/-!
# Entry 468 — generic scan loop: consume a unary field `skipOnesRight` (proved)

The first component of a **fixed-size generic rule-table scan loop** (the construction the fixed universal `U` needs — see
the fixed-`U` finding in entry 467; the unrolled `matchTable3` is *not* fixed).  A generic loop must parse the rule table
one record at a time using a *constant* number of states, with the head position encoding progress — exactly the
distance-agnostic pattern of `seekMarkRight` (entry 388).

Records are self-delimiting: each is a unary field (`I`s) terminated by the separator `O`, then a symbol.  So a generic
loop must **consume a unary field** — walk right over `I`s until a non-`I` cell.  This brick is that loop:
`skipOnesRight s stop cont := branchOne3 s cont stop ++ moveRight3 cont s` — a fixed 3-state machine (`s`, `cont`, `stop`)
with a back-edge (`cont → s`), driving any distance.

## What is proved (clean axioms, no `sorry`)

* **`branchOne3 s sCont sStop`** — at the head, *stay*; go to `sCont` if the cell is `I`, else (`O`/`M`) to `sStop`.
  **`branchOne3_run_one`** / **`branchOne3_run_stop`** (PROVED) — the two branches (tape identical).
* **`skipOnesRight s stop cont`** — the unary-consume loop.  **`skipOnesRight_run`** (PROVED) — if `h … h+d-1` are all
  `I` and `h+d` is non-`I`, the machine drives `(s, h, tp) → (stop, h+d, tp)` (`∃` step count), tape identical — by
  induction on `d`, machine fixed.

## Honest scope

This is **one fixed-state loop component** of the generic scan loop.  It does **not** yet build the per-record key
comparison, the record-advance, the table-end test, the full scan loop, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building
those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnes

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3 writeAt3_id_of_lt)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The branch-on-one machine.**  At the head, *stay*; go to `sCont` if the cell is `I`, else (`O`/`M`) to `sStop`. -/
def branchOne3 (s sCont sStop : ℕ) : TMachine3 :=
  [((s, Sym3.I), (sCont, Sym3.I, (2 : Move))), ((s, Sym3.O), (sStop, Sym3.O, (2 : Move))),
   ((s, Sym3.M), (sStop, Sym3.M, (2 : Move)))]

/-- **`branchOne3` on `I` (PROVED).** -/
theorem branchOne3_run_one (s sCont sStop j : ℕ) (tp : List Sym3)
    (h : readSym3 (s, j, tp) = Sym3.I) (hbound : j < tp.length) :
    reachIn (toNTM3 (branchOne3 s sCont sStop)) 1 (s, j, tp) (sCont, j, tp) := by
  refine ⟨(sCont, j, tp), ?_, rfl⟩
  have hstep : concreteStep3 (branchOne3 s sCont sStop) (s, j, tp) (sCont, j, writeAt3 tp j Sym3.I) :=
    ⟨((s, Sym3.I), (sCont, Sym3.I, (2 : Move))), by simp [branchOne3], by simp [h], by simp [applyTrans3, moveHead]⟩
  rwa [show writeAt3 tp j Sym3.I = tp from by rw [← h]; exact writeAt3_id_of_lt tp j hbound] at hstep

/-- **`branchOne3` off `I` (PROVED).** -/
theorem branchOne3_run_stop (s sCont sStop j : ℕ) (tp : List Sym3)
    (hne : readSym3 (s, j, tp) ≠ Sym3.I) (hbound : j < tp.length) :
    reachIn (toNTM3 (branchOne3 s sCont sStop)) 1 (s, j, tp) (sStop, j, tp) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · refine ⟨(sStop, j, tp), ?_, rfl⟩
    have hstep : concreteStep3 (branchOne3 s sCont sStop) (s, j, tp) (sStop, j, writeAt3 tp j Sym3.O) :=
      ⟨((s, Sym3.O), (sStop, Sym3.O, (2 : Move))), by simp [branchOne3], by simp [h], by simp [applyTrans3, moveHead]⟩
    rwa [show writeAt3 tp j Sym3.O = tp from by rw [← h]; exact writeAt3_id_of_lt tp j hbound] at hstep
  · exact absurd h hne
  · refine ⟨(sStop, j, tp), ?_, rfl⟩
    have hstep : concreteStep3 (branchOne3 s sCont sStop) (s, j, tp) (sStop, j, writeAt3 tp j Sym3.M) :=
      ⟨((s, Sym3.M), (sStop, Sym3.M, (2 : Move))), by simp [branchOne3], by simp [h], by simp [applyTrans3, moveHead]⟩
    rwa [show writeAt3 tp j Sym3.M = tp from by rw [← h]; exact writeAt3_id_of_lt tp j hbound] at hstep

/-- **The consume-unary-field (rightward) machine (cyclic).**  Loop head `s`: on `I` move one cell right and loop;
on a non-`I` cell go to `stop`. -/
def skipOnesRight (s stop cont : ℕ) : TMachine3 :=
  branchOne3 s cont stop ++ moveRight3 cont s

/-- **The unary-consume loop reaches the delimiter (PROVED).**  With `h … h+d-1` all `I` and `h+d` non-`I`, the machine
goes from `(s, h, tp)` to `(stop, h+d, tp)`, tape identical. -/
theorem skipOnesRight_run (s stop cont : ℕ) (tp : List Sym3) :
    ∀ (d h : ℕ), (∀ k, k < d → tp.getD (h + k) Sym3.O = Sym3.I) → tp.getD (h + d) Sym3.O ≠ Sym3.I →
      h + d < tp.length →
      ∃ N, reachIn (toNTM3 (skipOnesRight s stop cont)) N (s, h, tp) (stop, h + d, tp) := by
  intro d
  induction d with
  | zero =>
      intro h _ hstop _
      refine ⟨1, ?_⟩
      have hb := branchOne3_run_stop s cont stop h tp (by simpa using hstop) (by omega)
      exact reachIn_append_left3 (branchOne3 s cont stop) (moveRight3 cont s) 1 _ _ hb
  | succ d ih =>
      intro h hones hstop hbound
      have hcell : readSym3 (s, h, tp) = Sym3.I := by simpa using hones 0 (Nat.succ_pos d)
      have hb1 := branchOne3_run_one s cont stop h tp hcell (by omega)
      have lift1 := reachIn_append_left3 (branchOne3 s cont stop) (moveRight3 cont s) 1 _ _ hb1
      have hb2 := moveRight3_run_eq cont s h tp (by omega)
      have lift2 := reachIn_append_right3 (branchOne3 s cont stop) (moveRight3 cont s) 1 _ _ hb2
      have iter := (reachIn_add (toNTM3 (skipOnesRight s stop cont)) 1 1 _ _).mpr
        ⟨(cont, h, tp), lift1, lift2⟩
      obtain ⟨N, hrec⟩ := ih (h + 1)
        (fun k hk => by have := hones (k + 1) (by omega); simpa [show h + (k + 1) = h + 1 + k from by omega] using this)
        (by have := hstop; simpa [show h + 1 + d = h + (d + 1) from by omega] using this)
        (by omega)
      rw [show h + 1 + d = h + (d + 1) from by omega] at hrec
      refine ⟨(1 + 1) + N, ?_⟩
      exact (reachIn_add (toNTM3 (skipOnesRight s stop cont)) (1 + 1) N _ _).mpr
        ⟨(s, h + 1, tp), iter, hrec⟩

/-!
**The unary-consume loop, proved.**  `skipOnesRight` walks past a unary field regardless of length, a fixed-state
component of the generic scan loop.  Next: the per-record key comparison and record-advance, then the full fixed-size
rule-table scan loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnes

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnes.skipOnesRight_run

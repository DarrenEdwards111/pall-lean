import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MoveRightHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MoveClean

/-!
# Entry 441 — universal-TM-table build: chaining two home-to-home phases `twoMoveRight3` (proved)

The first concrete *master-sequence* composition: chain two home-to-home right-move phases (entry 439) into one machine
that advances the simulated head right **twice** and returns to the config home.  The point is the chaining mechanism — the
second phase's hypotheses are discharged from the first phase's output using the invariant-preservation lemma (entry 440),
so the two phases compose by `reachIn_seq3` with the marker invariant carried across.

## What is proved (clean axioms, no `sorry`)

* **`movedRight tp p`** — `writeAt3 (writeAt3 tp p (tp.getD (p+1) O)) (p+1) M`, the tape after one right move at marker `p`.
* **`twoMoveRight3 <phase-1 states> <phase-2 states>`** — `moveRightFromHome3 … ++ moveRightFromHome3 …`.
* **`twoMoveRight3_run`** (PROVED) — with the home/head markers, a clean window `(home, p)`, the next two cells `p+1`,
  `p+2` bits, and bounds: `∃ N, reachIn N (a0, home+1, tp) (out2, home+1, movedRight (movedRight tp p) (p+1))` — from the
  config home, the head marker advances `p → p+1 → p+2` and the head returns home; the second phase's preconditions come
  from `moveRight_preserves_clean` (entry 440) applied to the first phase's output.

## Honest scope

This is the **two-phase chain** — proof that home-to-home phases compose with the marker invariant carried across.  It does
**not** generalise to an arbitrary number of steps, the heterogeneous (lookup/apply/refresh) phases, nor `EmitsEncodedStep3`.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TwoMove

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveRightHome (moveRightFromHome3 moveRightFromHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveClean (moveRight_preserves_clean)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- The tape after one right move at marker `p`. -/
def movedRight (tp : List Sym3) (p : ℕ) : List Sym3 :=
  writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (w : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

/-- One right move preserves length (in bounds). -/
private theorem movedRight_length (tp : List Sym3) (p : ℕ) (h2 : p + 1 < tp.length) :
    (movedRight tp p).length = tp.length := by
  have hin : (writeAt3 tp p (tp.getD (p + 1) Sym3.O)).length = tp.length := writeAt3_length_eq tp p _ (by omega)
  show (writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M).length = tp.length
  rw [writeAt3_length_eq _ (p + 1) Sym3.M (by rw [hin]; omega), hin]

/-- **Chain two home-to-home right moves.** -/
def twoMoveRight3 (a0 a1 a2 a3 a4 a5 a6 a7 a8 mid b1 b2 b3 b4 b5 b6 b7 b8 out2 : ℕ) : TMachine3 :=
  moveRightFromHome3 a0 a1 a2 a3 a4 a5 a6 a7 a8 mid ++ moveRightFromHome3 mid b1 b2 b3 b4 b5 b6 b7 b8 out2

/-- **The two-move chain run (PROVED).**  From the config home, advance the head right twice and return home. -/
theorem twoMoveRight3_run (a0 a1 a2 a3 a4 a5 a6 a7 a8 mid b1 b2 b3 b4 b5 b6 b7 b8 out2 home p : ℕ) (tp : List Sym3)
    (hhp : home < p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc1 : tp.getD (p + 1) Sym3.O = Sym3.O ∨ tp.getD (p + 1) Sym3.O = Sym3.I)
    (hc2 : tp.getD (p + 2) Sym3.O = Sym3.O ∨ tp.getD (p + 2) Sym3.O = Sym3.I)
    (hbnd1 : p + 1 < tp.length) (hbnd2 : p + 2 < tp.length) :
    ∃ N, reachIn (toNTM3 (twoMoveRight3 a0 a1 a2 a3 a4 a5 a6 a7 a8 mid b1 b2 b3 b4 b5 b6 b7 b8 out2)) N
      (a0, home + 1, tp) (out2, home + 1, movedRight (movedRight tp p) (p + 1)) := by
  obtain ⟨N1, h1⟩ := moveRightFromHome3_run a0 a1 a2 a3 a4 a5 a6 a7 a8 mid home p tp hhp hmarkHome hmarkHead hclean hc1 hbnd1
  obtain ⟨hm1, hm2, hm3⟩ := moveRight_preserves_clean tp home p hhp hmarkHome hclean hc1
  have hc2' : (movedRight tp p).getD ((p + 1) + 1) Sym3.O = Sym3.O ∨ (movedRight tp p).getD ((p + 1) + 1) Sym3.O = Sym3.I := by
    unfold movedRight
    rw [writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]
    exact hc2
  have hbnd2' : (p + 1) + 1 < (movedRight tp p).length := by rw [movedRight_length tp p hbnd1]; omega
  obtain ⟨N2, h2⟩ := moveRightFromHome3_run mid b1 b2 b3 b4 b5 b6 b7 b8 out2 home (p + 1) (movedRight tp p)
    (by omega) hm1 hm2 hm3 hc2' hbnd2'
  exact ⟨N1 + N2, reachIn_seq3 (moveRightFromHome3 a0 a1 a2 a3 a4 a5 a6 a7 a8 mid)
    (moveRightFromHome3 mid b1 b2 b3 b4 b5 b6 b7 b8 out2) N1 N2 _ _ _ h1 h2⟩

/-!
**Chaining two home-to-home phases, proved.**  `twoMoveRight3` advances the head right twice and returns home — the second
phase justified from the first's output via the invariant-preservation lemma (entry 440).  This is the master-sequence
chaining mechanism in miniature.  Next: generalise to many phases / heterogeneous phases, and assemble `EmitsEncodedStep3`
— fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TwoMove

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TwoMove.twoMoveRight3_run

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteSymHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MoveRightHome

/-!
# Entry 449 — universal-TM-table build: the write-then-move apply core `applyWriteMoveRight3` (proved)

The core tape transformation of one simulated TM step (rightward case), as a single **home-to-home** machine: write the
rule's symbol at the simulated current cell (`writeSymHome3`, entry 447), then advance the head right (`moveRightFromHome3`,
entry 439).  Under the marker-right-of-current-cell representation this is correct: the write puts `w` at the current cell
`p+1`, and the move *carries* that `w` to cell `p` (preserving it just left of the marker) while relocating the marker to
`p+1` — exactly "write then step right".

This is the first genuine **master-apply chain**: two heterogeneous home-to-home phases composed, the second phase's
hypotheses discharged from the first's output tape `writeAt3 tp (p+1) w` via `writeAt3_getD`.

## What is proved (clean axioms, no `sorry`)

* **`applyWriteMoveRight3 <write states> mid <move states>`** — `writeSymHome3 … mid w ++ moveRightFromHome3 mid …`.
* **`applyWriteMoveRight3_run`** (PROVED) — with the home marker, the head marker at `p` (`home < p`), no other marker in
  `(home, p)`, the write symbol `w` a bit, and `p+1 < tp.length`: `∃ N, reachIn N (a, home+1, tp) (outM, home+1, writeAt3
  (writeAt3 (writeAt3 tp (p+1) w) p w) (p+1) M)` — the symbol `w` is written and carried to cell `p`, the marker advances
  to `p+1`, and the head returns to the config home.

## Honest scope

This is the **write-then-move apply core** (rightward).  It does **not** yet add the cache-refresh / state-update phases
(which have their own integration), nor assemble `EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ApplyWriteMove

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteSymHome (writeSymHome3 writeSymHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveRightHome (moveRightFromHome3 moveRightFromHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (v : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q v).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

/-- **The write-then-move apply core.**  Write `w` at the current cell, then advance the head right. -/
def applyWriteMoveRight3 (a aF aC b c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 outM : ℕ) (w : Sym3) :
    TMachine3 :=
  writeSymHome3 a aF aC b c cF cC dd dF dC mid w ++ moveRightFromHome3 mid sFound sCont s1 f1 c1 s2 f2 c2 outM

/-- **The write-then-move apply-core run (PROVED).**  Writes `w` at the current cell, carries it to `p`, advances the
marker to `p+1`, head returns home. -/
theorem applyWriteMoveRight3_run (a aF aC b c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 outM home p : ℕ)
    (w : Sym3) (tp : List Sym3) (hhp : home < p) (hmarkHome : tp.getD home Sym3.O = Sym3.M)
    (hmarkHead : tp.getD p Sym3.O = Sym3.M) (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hw : w = Sym3.O ∨ w = Sym3.I) (hbnd : p + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (applyWriteMoveRight3 a aF aC b c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 outM w)) N
      (a, home + 1, tp) (outM, home + 1, writeAt3 (writeAt3 (writeAt3 tp (p + 1) w) p w) (p + 1) Sym3.M) := by
  obtain ⟨N1, h1⟩ := writeSymHome3_run a aF aC b c cF cC dd dF dC mid home p w tp hhp hmarkHome hmarkHead hclean hw hbnd
  have hX : ∀ q : ℕ, q ≠ p + 1 → (writeAt3 tp (p + 1) w).getD q Sym3.O = tp.getD q Sym3.O := by
    intro q hq; rw [writeAt3_getD, if_neg hq]
  have hmH : (writeAt3 tp (p + 1) w).getD home Sym3.O = Sym3.M := by rw [hX home (by omega)]; exact hmarkHome
  have hmHead : (writeAt3 tp (p + 1) w).getD p Sym3.O = Sym3.M := by rw [hX p (by omega)]; exact hmarkHead
  have hcl : ∀ j, home < j → j < p → (writeAt3 tp (p + 1) w).getD j Sym3.O ≠ Sym3.M := by
    intro j hj1 hj2; rw [hX j (by omega)]; exact hclean j hj1 hj2
  have hgetp1 : (writeAt3 tp (p + 1) w).getD (p + 1) Sym3.O = w := by rw [writeAt3_getD, if_pos rfl]
  have hcc : (writeAt3 tp (p + 1) w).getD (p + 1) Sym3.O = Sym3.O ∨ (writeAt3 tp (p + 1) w).getD (p + 1) Sym3.O = Sym3.I := by
    rw [hgetp1]; exact hw
  obtain ⟨N2, h2⟩ := moveRightFromHome3_run mid sFound sCont s1 f1 c1 s2 f2 c2 outM home p (writeAt3 tp (p + 1) w)
    hhp hmH hmHead hcl hcc (by rw [writeAt3_length_eq tp (p + 1) w hbnd]; omega)
  rw [hgetp1] at h2
  exact ⟨N1 + N2, reachIn_seq3 (writeSymHome3 a aF aC b c cF cC dd dF dC mid w)
    (moveRightFromHome3 mid sFound sCont s1 f1 c1 s2 f2 c2 outM) N1 N2 _ _ _ h1 h2⟩

/-!
**The write-then-move apply core, proved.**  `applyWriteMoveRight3` writes the rule's symbol and steps the head right in
one home-to-home machine — the first heterogeneous master-apply chain.  Next: the left variant / dispatch, the cache-refresh
and state-update phases, and the matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified fragment,
not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ApplyWriteMove

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ApplyWriteMove.applyWriteMoveRight3_run

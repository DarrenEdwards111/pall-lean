import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HeadRightHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HeadLeftHome

/-!
# Entry 438 — universal-TM-table build: the move-direction dispatch `moveHeadDispatch3` (proved)

The simulated head move must go left or right according to the matched rule.  By the time the apply runs, that direction
is carried in the *control state* (the matcher routes to a "move-right" or "move-left" state), so the honest realisation is
a **dispatch**: one machine that holds both canonical move phases (entries 436, 437), entered at `sR` for a right move or
`sL` for a left move.  The caller's entry state selects the branch; the unused phase is never entered (lifted into the
union by `reachIn_append_left3`/`reachIn_append_right3`).

Both phases return to the config home `home+1`, so whichever direction is taken, the head ends canonically.

## What is proved (clean axioms, no `sorry`)

* **`moveHeadDispatch3 <right states> <left states>`** — `headRightReturnHome3 … ++ headLeftReturnHome3 …`.
* **`moveHeadDispatch3_run_right`** (PROVED) — entered at the right-entry state, runs the right move phase: marker `p →
  p+1`, head to `home+1`.
* **`moveHeadDispatch3_run_left`** (PROVED) — entered at the left-entry state, runs the left move phase: marker `p → p-1`,
  head to `home+1`.

## Honest scope

This is the **move-direction dispatch** — both phases under one machine, selected by entry state.  It does **not** yet
prepend the home-to-marker seek, nor connect the entry state to the matched rule's move bit, nor assemble the full step /
`EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveDispatch

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadRightHome (headRightReturnHome3 headRightReturnHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadLeftHome (headLeftReturnHome3 headLeftReturnHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The move-direction dispatch.**  Both canonical move phases under one machine; the entry state selects. -/
def moveHeadDispatch3 (sR sR1 fR1 cR1 sR2 fR2 cR2 outR sL sL1 fL1 cL1 sL2 fL2 cL2 outL : ℕ) : TMachine3 :=
  headRightReturnHome3 sR sR1 fR1 cR1 sR2 fR2 cR2 outR ++ headLeftReturnHome3 sL sL1 fL1 cL1 sL2 fL2 cL2 outL

/-- **Right-entry dispatch run (PROVED).**  Entered at `sR`, runs the right move phase. -/
theorem moveHeadDispatch3_run_right
    (sR sR1 fR1 cR1 sR2 fR2 cR2 outR sL sL1 fL1 cL1 sL2 fL2 cL2 outL home p : ℕ) (tp : List Sym3)
    (hhp : home < p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p + 1) Sym3.O = Sym3.O ∨ tp.getD (p + 1) Sym3.O = Sym3.I) (hbnd : p + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (moveHeadDispatch3 sR sR1 fR1 cR1 sR2 fR2 cR2 outR sL sL1 fL1 cL1 sL2 fL2 cL2 outL)) N
      (sR, p, tp) (outR, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M) := by
  obtain ⟨N, h⟩ := headRightReturnHome3_run sR sR1 fR1 cR1 sR2 fR2 cR2 outR home p tp hhp hmarkHome hmarkHead hclean hc hbnd
  exact ⟨N, reachIn_append_left3 (headRightReturnHome3 sR sR1 fR1 cR1 sR2 fR2 cR2 outR)
    (headLeftReturnHome3 sL sL1 fL1 cL1 sL2 fL2 cL2 outL) N _ _ h⟩

/-- **Left-entry dispatch run (PROVED).**  Entered at `sL`, runs the left move phase. -/
theorem moveHeadDispatch3_run_left
    (sR sR1 fR1 cR1 sR2 fR2 cR2 outR sL sL1 fL1 cL1 sL2 fL2 cL2 outL home p : ℕ) (tp : List Sym3)
    (hhp : home + 2 ≤ p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p - 1) Sym3.O = Sym3.O ∨ tp.getD (p - 1) Sym3.O = Sym3.I) (hbnd : p < tp.length) :
    ∃ N, reachIn (toNTM3 (moveHeadDispatch3 sR sR1 fR1 cR1 sR2 fR2 cR2 outR sL sL1 fL1 cL1 sL2 fL2 cL2 outL)) N
      (sL, p, tp) (outL, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M) := by
  obtain ⟨N, h⟩ := headLeftReturnHome3_run sL sL1 fL1 cL1 sL2 fL2 cL2 outL home p tp hhp hmarkHome hmarkHead hclean hc hbnd
  exact ⟨N, reachIn_append_right3 (headRightReturnHome3 sR sR1 fR1 cR1 sR2 fR2 cR2 outR)
    (headLeftReturnHome3 sL sL1 fL1 cL1 sL2 fL2 cL2 outL) N _ _ h⟩

/-!
**The move-direction dispatch, proved.**  `moveHeadDispatch3` holds both canonical move phases; the entry state selects the
direction and either way the head returns to the config home.  Next: connect the entry state to the matched rule's move bit
(the matcher routes here), prepend the home-to-marker seek, and assemble the full simulated step toward `EmitsEncodedStep3`
— fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveDispatch

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveDispatch.moveHeadDispatch3_run_right
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveDispatch.moveHeadDispatch3_run_left

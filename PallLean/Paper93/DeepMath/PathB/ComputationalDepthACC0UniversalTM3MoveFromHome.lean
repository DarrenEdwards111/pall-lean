import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MoveRightHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MoveLeftHome

/-!
# Entry 443 — universal-TM-table build: the home-to-home move dispatch `moveFromHome3` (proved)

The apply's head-move phase as a single **home-to-home** dispatch: one machine holding both home-to-home move phases
(entries 439, 442), entered at the right-entry state `sR` for a right move or the left-entry state `sL` for a left move
(the direction carried in the control state, set by the matched rule).  The entry state selects; both start and end at the
config home, so this is one drop-in master-sequence phase regardless of direction.

## What is proved (clean axioms, no `sorry`)

* **`moveFromHome3 <right states> <left states>`** — `moveRightFromHome3 … ++ moveLeftFromHome3 …`.
* **`moveFromHome3_run_right`** (PROVED) — entered at the right-entry state: home-to-home right move.
* **`moveFromHome3_run_left`** (PROVED) — entered at the left-entry state: home-to-home left move.

## Honest scope

This is the **home-to-home move dispatch** — the apply's move phase, drop-in for either direction.  It does **not** yet
connect the entry state to the matched rule's move bit, nor assemble `EmitsEncodedStep3`.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveFromHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveRightHome (moveRightFromHome3 moveRightFromHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveLeftHome (moveLeftFromHome3 moveLeftFromHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The home-to-home move dispatch.**  Both home-to-home move phases under one machine; the entry state selects. -/
def moveFromHome3 (rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO : ℕ) : TMachine3 :=
  moveRightFromHome3 rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO ++ moveLeftFromHome3 lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO

/-- **Right-entry move-from-home (PROVED).**  Entered at `rS`, a home-to-home right move. -/
theorem moveFromHome3_run_right
    (rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO home p : ℕ) (tp : List Sym3)
    (hhp : home < p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p + 1) Sym3.O = Sym3.O ∨ tp.getD (p + 1) Sym3.O = Sym3.I) (hbnd : p + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (moveFromHome3 rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO)) N
      (rS, home + 1, tp) (rO, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M) := by
  obtain ⟨N, h⟩ := moveRightFromHome3_run rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO home p tp hhp hmarkHome hmarkHead hclean hc hbnd
  exact ⟨N, reachIn_append_left3 (moveRightFromHome3 rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO)
    (moveLeftFromHome3 lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO) N _ _ h⟩

/-- **Left-entry move-from-home (PROVED).**  Entered at `lS`, a home-to-home left move. -/
theorem moveFromHome3_run_left
    (rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO home p : ℕ) (tp : List Sym3)
    (hhp : home + 2 ≤ p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p - 1) Sym3.O = Sym3.O ∨ tp.getD (p - 1) Sym3.O = Sym3.I) (hbnd : p < tp.length) :
    ∃ N, reachIn (toNTM3 (moveFromHome3 rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO)) N
      (lS, home + 1, tp) (lO, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M) := by
  obtain ⟨N, h⟩ := moveLeftFromHome3_run lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO home p tp hhp hmarkHome hmarkHead hclean hc hbnd
  exact ⟨N, reachIn_append_right3 (moveRightFromHome3 rS rF rC r1 rf1 rc1 r2 rf2 rc2 rO)
    (moveLeftFromHome3 lS lF lC l1 lf1 lc1 l2 lf2 lc2 lO) N _ _ h⟩

/-!
**The home-to-home move dispatch, proved.**  `moveFromHome3` is the apply's move phase: a single home-to-home operation
selecting direction by entry state.  Next: connect the entry state to the matched rule's move bit, and assemble the full
step toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveFromHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveFromHome.moveFromHome3_run_right
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveFromHome.moveFromHome3_run_left

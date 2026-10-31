import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HeadRightHome

/-!
# Entry 439 — universal-TM-table build: the home-to-home right move `moveRightFromHome3` (proved)

The canonical phases of entries 436–438 start at the head marker.  For the master step sequence we want **home-to-home**
phases (start *and* end at the config home `c = home+1`), so they chain by `reachIn_seq3` with no positioning glue.  This
brick makes the right head move home-to-home: from the config home, seek right to the head marker (`seekMarkRight`, entry
388), then advance the head right and return home (`headRightReturnHome3`, entry 436).

## What is proved (clean axioms, no `sorry`)

* **`moveRightFromHome3 sStart sFound sCont s1 f1 c1 s2 f2 c2 out`** — `seekMarkRight sStart sFound sCont ++
  headRightReturnHome3 sFound s1 f1 c1 s2 f2 c2 out`.
* **`moveRightFromHome3_run`** (PROVED) — with the home marker at `home`, the head marker at `p` (`home < p`), no other
  marker in `(home, p)`, the right neighbour `p+1` a bit, and `p+1 < tp.length`: `∃ N, reachIn N (sStart, home+1, tp) (out,
  home+1, writeAt3 (writeAt3 tp p (tp.getD (p+1) O)) (p+1) M)` — starting at the config home, the head marker advances `p →
  p+1` and the head returns to the config home: a home-to-home phase.

## Honest scope

This is the **home-to-home right move** — one phase of the master sequence, starting and ending canonically.  It does
**not** yet do the symmetric left/dispatch home-to-home, chain multiple phases (which needs the moved tape's cleanliness),
nor assemble the full step / `EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveRightHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadRightHome (headRightReturnHome3 headRightReturnHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The home-to-home right move.**  Seek from the config home to the head marker, then move right and return home. -/
def moveRightFromHome3 (sStart sFound sCont s1 f1 c1 s2 f2 c2 out : ℕ) : TMachine3 :=
  seekMarkRight sStart sFound sCont ++ headRightReturnHome3 sFound s1 f1 c1 s2 f2 c2 out

/-- **The home-to-home right-move run (PROVED).**  From the config home, advance the head right and return home. -/
theorem moveRightFromHome3_run (sStart sFound sCont s1 f1 c1 s2 f2 c2 out home p : ℕ) (tp : List Sym3)
    (hhp : home < p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p + 1) Sym3.O = Sym3.O ∨ tp.getD (p + 1) Sym3.O = Sym3.I) (hbnd : p + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (moveRightFromHome3 sStart sFound sCont s1 f1 c1 s2 f2 c2 out)) N (sStart, home + 1, tp)
      (out, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M) := by
  have hd : (home + 1) + (p - (home + 1)) = p := by omega
  obtain ⟨N1, hseek⟩ := seekMarkRight_run sStart sFound sCont tp (p - (home + 1)) (home + 1)
    (by rw [hd]; exact hmarkHead) (fun k hk => hclean (home + 1 + k) (by omega) (by omega)) (by rw [hd]; omega)
  rw [hd] at hseek
  obtain ⟨N2, hmove⟩ := headRightReturnHome3_run sFound s1 f1 c1 s2 f2 c2 out home p tp hhp hmarkHome hmarkHead hclean hc hbnd
  exact ⟨N1 + N2, reachIn_seq3 (seekMarkRight sStart sFound sCont)
    (headRightReturnHome3 sFound s1 f1 c1 s2 f2 c2 out) N1 N2 _ _ _ hseek hmove⟩

/-!
**The home-to-home right move, proved.**  `moveRightFromHome3` starts and ends at the config home — a phase that chains by
`reachIn_seq3` with no positioning glue.  Next: the symmetric left / dispatch home-to-home phases, chaining multiple phases
(threading the moved tape's cleanliness), and the full simulated step toward `EmitsEncodedStep3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveRightHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveRightHome.moveRightFromHome3_run

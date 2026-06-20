import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HeadLeftHome

/-!
# Entry 442 — universal-TM-table build: the home-to-home left move `moveLeftFromHome3` (proved)

The symmetric companion of entry 439: the **home-to-home** left head move.  From the config home, seek right to the head
marker (`seekMarkRight`, entry 388), then move the head left and return home (`headLeftReturnHome3`, entry 437).  Start and
end at the config home, so it chains by `reachIn_seq3`.

## What is proved (clean axioms, no `sorry`)

* **`moveLeftFromHome3 sStart sFound sCont s1 f1 c1 s2 f2 c2 out`** — `seekMarkRight sStart sFound sCont ++
  headLeftReturnHome3 sFound s1 f1 c1 s2 f2 c2 out`.
* **`moveLeftFromHome3_run`** (PROVED) — with the home marker at `home`, the head marker at `p` (`home+2 ≤ p`), no other
  marker in `(home, p)`, the left neighbour `p-1` a bit, and `p < tp.length`: `∃ N, reachIn N (sStart, home+1, tp) (out,
  home+1, writeAt3 (writeAt3 tp p (tp.getD (p-1) O)) (p-1) M)` — a home-to-home left move.

## Honest scope

This is the **home-to-home left move** — the second move phase.  It does **not** assemble `EmitsEncodedStep3`.  Building
the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveLeftHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadLeftHome (headLeftReturnHome3 headLeftReturnHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The home-to-home left move.**  Seek from the config home to the head marker, then move left and return home. -/
def moveLeftFromHome3 (sStart sFound sCont s1 f1 c1 s2 f2 c2 out : ℕ) : TMachine3 :=
  seekMarkRight sStart sFound sCont ++ headLeftReturnHome3 sFound s1 f1 c1 s2 f2 c2 out

/-- **The home-to-home left-move run (PROVED).**  From the config home, move the head left and return home. -/
theorem moveLeftFromHome3_run (sStart sFound sCont s1 f1 c1 s2 f2 c2 out home p : ℕ) (tp : List Sym3)
    (hhp : home + 2 ≤ p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p - 1) Sym3.O = Sym3.O ∨ tp.getD (p - 1) Sym3.O = Sym3.I) (hbnd : p < tp.length) :
    ∃ N, reachIn (toNTM3 (moveLeftFromHome3 sStart sFound sCont s1 f1 c1 s2 f2 c2 out)) N (sStart, home + 1, tp)
      (out, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M) := by
  have hd : (home + 1) + (p - (home + 1)) = p := by omega
  obtain ⟨N1, hseek⟩ := seekMarkRight_run sStart sFound sCont tp (p - (home + 1)) (home + 1)
    (by rw [hd]; exact hmarkHead) (fun k hk => hclean (home + 1 + k) (by omega) (by omega)) (by rw [hd]; omega)
  rw [hd] at hseek
  obtain ⟨N2, hmove⟩ := headLeftReturnHome3_run sFound s1 f1 c1 s2 f2 c2 out home p tp hhp hmarkHome hmarkHead hclean hc hbnd
  exact ⟨N1 + N2, reachIn_seq3 (seekMarkRight sStart sFound sCont)
    (headLeftReturnHome3 sFound s1 f1 c1 s2 f2 c2 out) N1 N2 _ _ _ hseek hmove⟩

/-!
**The home-to-home left move, proved.**  `moveLeftFromHome3` starts and ends at the config home.  Next: the from-home move
dispatch (right/left by entry state), and the full step toward `EmitsEncodedStep3` — fragment by verified fragment, not
faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveLeftHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveLeftHome.moveLeftFromHome3_run

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Move
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Unmark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SkipMark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome

/-!
# Entry 447 — universal-TM-table build: the home-to-home symbol write `writeSymHome3` (proved)

The last apply sub-phase: write the matched rule's symbol at the simulated current cell, as a **home-to-home** phase.  From
the config home, seek right to the head marker (`seekMarkRight`, 388), step onto the current cell (the cell after the
marker), write the symbol there (`unmark3`), then skip the head marker (`skipMarkLeft3`, 432) and reset to the config home
(`resetToHome3`, 408).  The head marker is unchanged (the write is at the current cell), the symbol is a parameter (set by
the matched rule, dispatched like the move direction).

## What is proved (clean axioms, no `sorry`)

* **`writeSymHome3 <states> w`** — `seekMarkRight … ++ moveRight3 … ++ unmark3 … w ++ skipMarkLeft3 … ++ resetToHome3 …`.
* **`writeSymHome3_run`** (PROVED) — with the home marker, the head marker at `p` (`home < p`), no other marker in
  `(home, p)`, the write symbol `w` a bit, and `p+1 < tp.length`: `∃ N, reachIn N (sStart, home+1, tp) (out, home+1,
  writeAt3 tp (p+1) w)` — the current cell `p+1` is set to `w` and the head returns to the config home.

## Honest scope

This is the **home-to-home symbol write** — the last apply sub-phase made canonical.  It does **not** assemble
`EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteSymHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipMark (skipMarkLeft3 skipMarkLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (v : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q v).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

/-- **The home-to-home symbol write.**  Seek to the marker, step onto the current cell, write `w`, return home. -/
def writeSymHome3 (a aF aC b c cF cC d dF dC out : ℕ) (w : Sym3) : TMachine3 :=
  seekMarkRight a aF aC ++ moveRight3 aF b ++ unmark3 b c w ++ skipMarkLeft3 c cF cC d ++ resetToHome3 d dF dC out

/-- **The home-to-home symbol-write run (PROVED).**  Sets the current cell `p+1` to `w` and returns to the config home. -/
theorem writeSymHome3_run (a aF aC b c cF cC d dF dC out home p : ℕ) (w : Sym3) (tp : List Sym3)
    (hhp : home < p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M) (hw : w = Sym3.O ∨ w = Sym3.I)
    (hbnd : p + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (writeSymHome3 a aF aC b c cF cC d dF dC out w)) N (a, home + 1, tp)
      (out, home + 1, writeAt3 tp (p + 1) w) := by
  have hd : (home + 1) + (p - (home + 1)) = p := by omega
  obtain ⟨N1, hseek⟩ := seekMarkRight_run a aF aC tp (p - (home + 1)) (home + 1)
    (by rw [hd]; exact hmarkHead) (fun k hk => hclean (home + 1 + k) (by omega) (by omega)) (by rw [hd]; omega)
  rw [hd] at hseek
  have hmr := moveRight3_run_eq aF b p tp (by omega)
  have hun := unmark3_run b c w (p + 1) tp
  set RT := writeAt3 tp (p + 1) w with hRT
  have hRTlen : RT.length = tp.length := by rw [hRT]; exact writeAt3_length_eq tp (p + 1) w hbnd
  have hmarkHead' : RT.getD p Sym3.O = Sym3.M := by rw [hRT, writeAt3_getD, if_neg (by omega)]; exact hmarkHead
  have hno' : ∀ k, 0 < k → k ≤ 1 → RT.getD (p + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    have : k = 1 := by omega
    subst this
    rw [hRT, writeAt3_getD, if_pos rfl]
    rcases hw with hb | hb <;> rw [hb] <;> decide
  obtain ⟨N4, hskip⟩ := skipMarkLeft3_run c cF cC d p 1 RT hmarkHead' hno' (by rw [hRTlen]; omega)
  have hmarkHome' : RT.getD home Sym3.O = Sym3.M := by rw [hRT, writeAt3_getD, if_neg (by omega)]; exact hmarkHome
  have hnoHome' : ∀ k, 0 < k → k ≤ p - 1 - home → RT.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    rw [hRT, writeAt3_getD, if_neg (by omega)]
    exact hclean (home + k) (by omega) (by omega)
  obtain ⟨N5, hreset⟩ := resetToHome3_run d dF dC out home (p - 1 - home) RT hmarkHome' hnoHome' (by rw [hRTlen]; omega)
  rw [show home + (p - 1 - home) = p - 1 from by omega] at hreset
  -- chain the five phases
  have s1 := reachIn_seq3 (seekMarkRight a aF aC) (moveRight3 aF b) N1 1 _ _ _ hseek hmr
  have s2 := reachIn_seq3 (seekMarkRight a aF aC ++ moveRight3 aF b) (unmark3 b c w) (N1 + 1) 1 _ _ _ s1 hun
  have s3 := reachIn_seq3 (seekMarkRight a aF aC ++ moveRight3 aF b ++ unmark3 b c w) (skipMarkLeft3 c cF cC d)
    (N1 + 1 + 1) N4 _ _ _ s2 hskip
  exact ⟨N1 + 1 + 1 + N4 + N5, reachIn_seq3
    (seekMarkRight a aF aC ++ moveRight3 aF b ++ unmark3 b c w ++ skipMarkLeft3 c cF cC d)
    (resetToHome3 d dF dC out) (N1 + 1 + 1 + N4) N5 _ _ _ s3 hreset⟩

/-!
**The home-to-home symbol write, proved.**  `writeSymHome3` sets the current cell to the rule's symbol and returns home —
the last apply sub-phase made canonical.  Next: the master apply sequence (state update + symbol write + move + cache
refresh, all home-to-home) and the matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteSymHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteSymHome.writeSymHome3_run

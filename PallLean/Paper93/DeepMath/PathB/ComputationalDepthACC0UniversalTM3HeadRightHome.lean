import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HeadMove
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SkipMark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome

/-!
# Entry 436 — universal-TM-table build: advance the head right and return home `headRightReturnHome3` (proved)

Top-level sequencing of the simulated step is clean only if each phase ends at a *canonical* position.  This brick
establishes the **return-to-home discipline** for the right head move: from the simulated head marker, move it one cell
right (`headMoveRight3`, entry 419), skip the (now relocated) head marker (`skipMarkLeft3`, entry 432), and reset to the
config home (`resetToHome3`, entry 408).  The phase starts at the head marker and ends at the config key start `c =
home+1`, so it composes trivially with the next phase.

## What is proved (clean axioms, no `sorry`)

* **`headRightReturnHome3 s s1 f1 c1 s2 f2 c2 out`** — `headMoveRight3 s s1 ++ skipMarkLeft3 s1 f1 c1 s2 ++ resetToHome3 s2
  f2 c2 out`.
* **`headRightReturnHome3_run`** (PROVED) — with the home marker at `home`, the head marker at `p` (`home < p`), no other
  marker in `(home, p)`, the right neighbour `p+1` a bit, and `p+1 < tp.length`: `∃ N, reachIn N (s, p, tp) (out, home+1,
  writeAt3 (writeAt3 tp p (tp.getD (p+1) O)) (p+1) M)` — the head marker has advanced to `p+1` and the head has returned to
  the config home, the tape being the moved tape.

## Honest scope

This is the **right head move with return-to-home** — the canonical-endpoint discipline for one phase.  It does **not** yet
prepend the seek from home to the marker, branch on move direction, nor assemble the full step / `EmitsEncodedStep3`.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadRightHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadMove (headMoveRight3 headMoveRight3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipMark (skipMarkLeft3 skipMarkLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Advance the head right and return home.**  Move the head marker right, skip it, reset to the config home. -/
def headRightReturnHome3 (s s1 f1 c1 s2 f2 c2 out : ℕ) : TMachine3 :=
  headMoveRight3 s s1 ++ skipMarkLeft3 s1 f1 c1 s2 ++ resetToHome3 s2 f2 c2 out

/-- **The advance-right-return-home run (PROVED).**  Marker `p → p+1`, head returns to `home+1`, tape is the moved tape. -/
theorem headRightReturnHome3_run (s s1 f1 c1 s2 f2 c2 out home p : ℕ) (tp : List Sym3)
    (hhp : home < p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (_hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p + 1) Sym3.O = Sym3.O ∨ tp.getD (p + 1) Sym3.O = Sym3.I) (hbnd : p + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (headRightReturnHome3 s s1 f1 c1 s2 f2 c2 out)) N (s, p, tp)
      (out, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M) := by
  obtain ⟨N1, h1⟩ := headMoveRight3_run s s1 p tp hc hbnd
  set tp' := writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M with htp'
  have hlen' : tp'.length = tp.length := by
    rw [htp']
    simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega
  -- skip the relocated head marker (now at p+1), landing just left of it
  have hmark' : tp'.getD (p + 1) Sym3.O = Sym3.M := by rw [htp', writeAt3_getD, if_pos rfl]
  obtain ⟨N2, h2⟩ := skipMarkLeft3_run s1 f1 c1 s2 (p + 1) 0 tp' hmark' (by intro k hk0 hk; omega) (by rw [hlen']; omega)
  -- reset to the config home
  have hmarkHome' : tp'.getD home Sym3.O = Sym3.M := by
    rw [htp', writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]; exact hmarkHome
  have hno' : ∀ k, 0 < k → k ≤ p - home → tp'.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    rcases Nat.lt_or_ge (home + k) p with hlt | hge
    · rw [htp', writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]
      exact hclean (home + k) (by omega) hlt
    · have hkp : home + k = p := by omega
      rw [hkp, htp', writeAt3_getD, if_neg (by omega), writeAt3_getD, if_pos rfl]
      rcases hc with hb | hb <;> rw [hb] <;> decide
  obtain ⟨N3, h3⟩ := resetToHome3_run s2 f2 c2 out home (p - home) tp' hmarkHome' hno' (by rw [hlen']; omega)
  rw [show home + (p - home) = p from by omega] at h3
  have s12 := reachIn_seq3 (headMoveRight3 s s1) (skipMarkLeft3 s1 f1 c1 s2) N1 N2 _ _ _ h1 h2
  exact ⟨N1 + N2 + N3, reachIn_seq3 (headMoveRight3 s s1 ++ skipMarkLeft3 s1 f1 c1 s2)
    (resetToHome3 s2 f2 c2 out) (N1 + N2) N3 _ _ _ s12 h3⟩

/-!
**Advance the head right and return home, proved.**  `headRightReturnHome3` moves the simulated head right and leaves the
head on the config key start — a phase with a canonical endpoint, the discipline that makes top-level sequencing compose.
Next: the symmetric left move, the home-to-marker seek, the move-direction branch, and the full simulated step toward
`EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadRightHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadRightHome.headRightReturnHome3_run

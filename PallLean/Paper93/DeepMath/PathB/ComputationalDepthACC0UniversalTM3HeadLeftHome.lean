import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HeadMove
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SkipMark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome

/-!
# Entry 437 — universal-TM-table build: advance the head left and return home `headLeftReturnHome3` (proved)

The symmetric companion of entry 436: the left head move with the return-to-home discipline.  From the simulated head
marker, move it one cell left (`headMoveLeft3`, entry 419), skip the relocated head marker (`skipMarkLeft3`, entry 432),
and reset to the config home (`resetToHome3`, entry 408).  The phase ends at the config key start `c = home+1`, so it
composes trivially — and pairs with entry 436 to give both move directions as canonical phases for the move-direction
branch.

## What is proved (clean axioms, no `sorry`)

* **`headLeftReturnHome3 s s1 f1 c1 s2 f2 c2 out`** — `headMoveLeft3 s s1 ++ skipMarkLeft3 s1 f1 c1 s2 ++ resetToHome3 s2
  f2 c2 out`.
* **`headLeftReturnHome3_run`** (PROVED) — with the home marker at `home`, the head marker at `p` (`home+2 ≤ p`), no other
  marker in `(home, p)`, the left neighbour `p-1` a bit, and `p < tp.length`: `∃ N, reachIn N (s, p, tp) (out, home+1,
  writeAt3 (writeAt3 tp p (tp.getD (p-1) O)) (p-1) M)` — the head marker has retreated to `p-1` and the head has returned
  to the config home, the tape being the moved tape.

## Honest scope

This is the **left head move with return-to-home** — the symmetric canonical phase.  It does **not** yet prepend the
home-to-marker seek, branch on move direction, nor assemble the full step / `EmitsEncodedStep3`.  Building those fragment
by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadLeftHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadMove (headMoveLeft3 headMoveLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipMark (skipMarkLeft3 skipMarkLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Advance the head left and return home.**  Move the head marker left, skip it, reset to the config home. -/
def headLeftReturnHome3 (s s1 f1 c1 s2 f2 c2 out : ℕ) : TMachine3 :=
  headMoveLeft3 s s1 ++ skipMarkLeft3 s1 f1 c1 s2 ++ resetToHome3 s2 f2 c2 out

/-- **The advance-left-return-home run (PROVED).**  Marker `p → p-1`, head returns to `home+1`, tape is the moved tape. -/
theorem headLeftReturnHome3_run (s s1 f1 c1 s2 f2 c2 out home p : ℕ) (tp : List Sym3)
    (hhp : home + 2 ≤ p) (hmarkHome : tp.getD home Sym3.O = Sym3.M) (_hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p - 1) Sym3.O = Sym3.O ∨ tp.getD (p - 1) Sym3.O = Sym3.I) (hbnd : p < tp.length) :
    ∃ N, reachIn (toNTM3 (headLeftReturnHome3 s s1 f1 c1 s2 f2 c2 out)) N (s, p, tp)
      (out, home + 1, writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M) := by
  obtain ⟨N1, h1⟩ := headMoveLeft3_run s s1 p tp hc (by omega) hbnd
  set tp' := writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M with htp'
  have hlen' : tp'.length = tp.length := by
    rw [htp']
    simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega
  -- skip the relocated head marker (now at p-1), landing just left of it
  have hmark' : tp'.getD (p - 1) Sym3.O = Sym3.M := by rw [htp', writeAt3_getD, if_pos rfl]
  obtain ⟨N2, h2⟩ := skipMarkLeft3_run s1 f1 c1 s2 (p - 1) 0 tp' hmark' (by intro k hk0 hk; omega) (by rw [hlen']; omega)
  rw [show p - 1 - 1 = p - 2 from by omega] at h2
  -- reset to the config home
  have hmarkHome' : tp'.getD home Sym3.O = Sym3.M := by
    rw [htp', writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]; exact hmarkHome
  have hno' : ∀ k, 0 < k → k ≤ p - 2 - home → tp'.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    rw [htp', writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]
    exact hclean (home + k) (by omega) (by omega)
  obtain ⟨N3, h3⟩ := resetToHome3_run s2 f2 c2 out home (p - 2 - home) tp' hmarkHome' hno' (by rw [hlen']; omega)
  rw [show home + (p - 2 - home) = p - 2 from by omega] at h3
  have s12 := reachIn_seq3 (headMoveLeft3 s s1) (skipMarkLeft3 s1 f1 c1 s2) N1 N2 _ _ _ h1 h2
  exact ⟨N1 + N2 + N3, reachIn_seq3 (headMoveLeft3 s s1 ++ skipMarkLeft3 s1 f1 c1 s2)
    (resetToHome3 s2 f2 c2 out) (N1 + N2) N3 _ _ _ s12 h3⟩

/-!
**Advance the head left and return home, proved.**  `headLeftReturnHome3` moves the simulated head left and leaves the head
on the config key start — the symmetric canonical phase.  Next: the move-direction branch (select left/right by the rule's
move bit, the two-branch pattern), the home-to-marker seek, and the full simulated step toward `EmitsEncodedStep3` —
fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadLeftHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadLeftHome.headLeftReturnHome3_run

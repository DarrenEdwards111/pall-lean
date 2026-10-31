import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3StateUpdateHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyContent

/-!
# Entry 448 — universal-TM-table build: windowed-clean state update `clearStateField3_runW` / `clearStateFieldHome3_runW` (proved)

The marker-model reconciliation.  The state update (entries 430, 446) was proved with a **global** no-marker hypothesis
(`∀ j ≠ home, tp.getD j ≠ M`), which forbids a head marker — incompatible with the other apply phases (symbol-write, move,
cache-refresh), all of which carry a head marker `M` in the simulated tape.  This brick re-proves the state update with a
**windowed** clean hypothesis: no marker only in `(home, home+1+d'+newlen]` (the region the update touches and resets
through).  A head marker *beyond* `home+1+d'+newlen` (in the simulated tape, right of the rule region) is now permitted, so
all four apply phases share one marker model.

The key observation: the state update's *only* use of the global hypothesis was at the old field's separator cell, which
`hcoldsep` already pins to `O`; so `clearStateField3_runW` needs **no** clean hypothesis at all, and only the home-to-home
wrapper needs the windowed one (for its return reset across the gap and rule region).

## What is proved (clean axioms, no `sorry`)

* **`clearStateField3_runW`** (PROVED) — the state update, with **no** global clean hypothesis (separator covered by
  `hcoldsep`): same conclusion as entry 430.
* **`clearStateFieldHome3_runW`** (PROVED) — the home-to-home state update with the **windowed** clean hypothesis
  `∀ j, home < j → j ≤ home+1+d'+newlen → tp.getD j O ≠ M` (a head marker beyond the window is allowed).

## Honest scope

This is the **marker-model reconciliation** for the state update.  It does **not** yet chain the four phases into a master
apply, nor assemble `EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction,
**not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateWindowed

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk (walkRightClearField3 walkRightClearField3_run clearBlock)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Transfer (transferFieldLeft3 transferFieldLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft (copyBlockLeft)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdate (clearStateField3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateHome (clearStateFieldHome3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent (clearBlock_getD_outside clearBlock_getD_inside)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyContent (copyBlockLeft_getD_outside copyBlockLeft_getD_inside)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (v : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q v).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

private theorem clearBlock_length (tp : List Sym3) (h m : ℕ) (hb : h + m ≤ tp.length) :
    (clearBlock tp h m).length = tp.length := by
  induction m generalizing h tp with
  | zero => rfl
  | succ m ih =>
      show (clearBlock (writeAt3 tp h Sym3.O) (h + 1) m).length = tp.length
      rw [ih (writeAt3 tp h Sym3.O) (h + 1) (by rw [writeAt3_length_eq tp h Sym3.O (by omega)]; omega),
        writeAt3_length_eq tp h Sym3.O (by omega)]

private theorem copyBlockLeft_length (tp : List Sym3) (c d m : ℕ) (h : c + m < tp.length) (hd : d ≤ c) :
    (copyBlockLeft tp c d m).length = tp.length := by
  induction m generalizing c tp with
  | zero =>
      show (writeAt3 tp (c - d) (tp.getD c Sym3.O)).length = tp.length
      exact writeAt3_length_eq tp (c - d) _ (by omega)
  | succ m ih =>
      show (copyBlockLeft (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m).length = tp.length
      rw [ih (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1)
          (by rw [writeAt3_length_eq tp (c - d) _ (by omega)]; omega) (by omega),
        writeAt3_length_eq tp (c - d) _ (by omega)]

/-- **The state update with NO global clean hypothesis (PROVED).**  The separator cell is covered by `hcoldsep`. -/
theorem clearStateField3_runW (s sMid found cont mid d' sDone L1 L2 home oldlen newlen : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M) (hd' : 1 ≤ d') (hdold : oldlen < d') (hL1 : oldlen < L1) (hL2 : newlen < L2)
    (hbnd : home + 1 + d' + newlen < tp.length)
    (hcold : ∀ i, i < oldlen → tp.getD (home + 1 + i) Sym3.O = Sym3.I)
    (hcoldsep : tp.getD (home + 1 + oldlen) Sym3.O = Sym3.O)
    (hcnew : ∀ i, i < newlen → tp.getD (home + 1 + d' + i) Sym3.O = Sym3.I)
    (hcnewsep : tp.getD (home + 1 + d' + newlen) Sym3.O = Sym3.O) :
    ∃ N, reachIn (toNTM3 (clearStateField3 s sMid found cont mid d' sDone L1 L2)) N (s, home + 1, tp)
      (sDone, home + 1 + d' + newlen, copyBlockLeft (clearBlock tp (home + 1) oldlen) (home + 1 + d') d' newlen) := by
  obtain ⟨N1, hclear⟩ := walkRightClearField3_run sMid L1 s (home + 1) oldlen tp hL1 (by omega) hcold hcoldsep
  set tp' := clearBlock tp (home + 1) oldlen with htp'
  have hlen' : tp'.length = tp.length := clearBlock_length tp (home + 1) oldlen (by omega)
  have hmark' : tp'.getD home Sym3.O = Sym3.M := by
    rw [htp', clearBlock_getD_outside tp (home + 1) oldlen home (Or.inl (by omega))]; exact hmark
  have hno' : ∀ k, 0 < k → k ≤ oldlen + 1 → tp'.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hkd
    rcases Nat.lt_or_ge (home + k) (home + 1 + oldlen) with hlt | hge
    · rw [htp', clearBlock_getD_inside tp (home + 1) oldlen (home + k) (by omega) hlt]; decide
    · rw [htp', clearBlock_getD_outside tp (home + 1) oldlen (home + k) (Or.inr hge),
        show home + k = home + 1 + oldlen from by omega, hcoldsep]; decide
  have hcnew' : ∀ i, i < newlen → tp'.getD (home + 1 + d' + i) Sym3.O = Sym3.I := by
    intro i hi
    rw [htp', clearBlock_getD_outside tp (home + 1) oldlen (home + 1 + d' + i) (Or.inr (by omega))]
    exact hcnew i hi
  have hcnewsep' : tp'.getD (home + 1 + d' + newlen) Sym3.O = Sym3.O := by
    rw [htp', clearBlock_getD_outside tp (home + 1) oldlen (home + 1 + d' + newlen) (Or.inr (by omega))]
    exact hcnewsep
  obtain ⟨N2, htrans⟩ := transferFieldLeft3_run sMid found cont mid d' sDone L2 home (oldlen + 1) newlen tp'
    hmark' hno' (by rw [hlen']; omega) hL2 hd' (by rw [hlen']; omega) hcnew' hcnewsep'
  rw [show home + (oldlen + 1) = home + 1 + oldlen from by omega] at htrans
  exact ⟨N1 + N2, reachIn_seq3 (walkRightClearField3 s sMid L1) (transferFieldLeft3 sMid found cont mid d' sDone L2)
    N1 N2 _ _ _ hclear htrans⟩

/-- **The home-to-home state update with a WINDOWED clean hypothesis (PROVED).**  A head marker beyond
`home+1+d'+newlen` is permitted, so this shares the marker model of the other apply phases. -/
theorem clearStateFieldHome3_runW (s sMid found cont mid d' sDone L1 L2 rf rc rout home oldlen newlen : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M)
    (hcleanW : ∀ j, home < j → j ≤ home + 1 + d' + newlen → tp.getD j Sym3.O ≠ Sym3.M)
    (hd' : 1 ≤ d') (hdold : oldlen < d') (hnd : newlen < d') (hL1 : oldlen < L1) (hL2 : newlen < L2)
    (hbnd : home + 1 + d' + newlen < tp.length)
    (hcold : ∀ i, i < oldlen → tp.getD (home + 1 + i) Sym3.O = Sym3.I)
    (hcoldsep : tp.getD (home + 1 + oldlen) Sym3.O = Sym3.O)
    (hcnew : ∀ i, i < newlen → tp.getD (home + 1 + d' + i) Sym3.O = Sym3.I)
    (hcnewsep : tp.getD (home + 1 + d' + newlen) Sym3.O = Sym3.O) :
    ∃ N, reachIn (toNTM3 (clearStateFieldHome3 s sMid found cont mid d' sDone L1 L2 rf rc rout)) N (s, home + 1, tp)
      (rout, home + 1, copyBlockLeft (clearBlock tp (home + 1) oldlen) (home + 1 + d') d' newlen) := by
  obtain ⟨N1, h1⟩ := clearStateField3_runW s sMid found cont mid d' sDone L1 L2 home oldlen newlen tp hmark hd' hdold
    hL1 hL2 hbnd hcold hcoldsep hcnew hcnewsep
  set CB := clearBlock tp (home + 1) oldlen with hCB
  set RT := copyBlockLeft CB (home + 1 + d') d' newlen with hRT
  have hCBlen : CB.length = tp.length := clearBlock_length tp (home + 1) oldlen (by omega)
  have hRTlen : RT.length = tp.length := by
    rw [hRT, copyBlockLeft_length CB (home + 1 + d') d' newlen (by rw [hCBlen]; omega) (by omega)]; exact hCBlen
  have hmark_r : RT.getD home Sym3.O = Sym3.M := by
    rw [hRT, copyBlockLeft_getD_outside CB (home + 1 + d') d' newlen home hnd (by omega) (Or.inl (by omega)),
      hCB, clearBlock_getD_outside tp (home + 1) oldlen home (Or.inl (by omega))]
    exact hmark
  have hno_r : ∀ k, 0 < k → k ≤ d' + newlen + 1 → RT.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    rcases Nat.lt_or_ge (home + k) (home + 1 + newlen + 1) with hAdest | hBout
    · rw [hRT, copyBlockLeft_getD_inside CB (home + 1 + d') d' newlen (home + k) hnd (by omega) (by omega) (by omega),
        hCB, clearBlock_getD_outside tp (home + 1) oldlen (home + k + d') (Or.inr (by omega))]
      have hi : home + k + d' = home + 1 + d' + (k - 1) := by omega
      rw [hi]
      rcases Nat.lt_or_ge (k - 1) newlen with hin | hge
      · rw [hcnew (k - 1) hin]; decide
      · rw [show k - 1 = newlen from by omega, hcnewsep]; decide
    · rw [hRT, copyBlockLeft_getD_outside CB (home + 1 + d') d' newlen (home + k) hnd (by omega) (Or.inr (by omega)), hCB]
      rcases Nat.lt_or_ge (home + k) (home + 1 + oldlen) with hcl | hncl
      · rw [clearBlock_getD_inside tp (home + 1) oldlen (home + k) (by omega) hcl]; decide
      · rw [clearBlock_getD_outside tp (home + 1) oldlen (home + k) (Or.inr hncl)]
        exact hcleanW (home + k) (by omega) (by omega)
  obtain ⟨N2, h2⟩ := resetToHome3_run sDone rf rc rout home (d' + newlen + 1) RT hmark_r hno_r (by rw [hRTlen]; omega)
  rw [show home + (d' + newlen + 1) = home + 1 + d' + newlen from by omega] at h2
  exact ⟨N1 + N2, reachIn_seq3 (clearStateField3 s sMid found cont mid d' sDone L1 L2)
    (resetToHome3 sDone rf rc rout) N1 N2 _ _ _ h1 h2⟩

/-!
**The windowed-clean state update, proved.**  `clearStateFieldHome3_runW` runs the home-to-home state update under a
*windowed* clean hypothesis — a head marker beyond the rule region is permitted, so the four apply phases now share one
marker model.  Next: chain the four home-to-home phases into the master apply, then the matcher↔lookup correspondence toward
`EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateWindowed

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateWindowed.clearStateField3_runW
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateWindowed.clearStateFieldHome3_runW

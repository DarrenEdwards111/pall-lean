import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3StateUpdateWindowed
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CacheRefreshHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3TapeShift

/-!
# Entry 454 — universal-TM-table build: the full state update `stateUpdateFull3` (proved)

The complete simulated-**state** update that *correctly handles the variable-length unary state field* — without ever
shifting the marker-containing simulated tape.  The insight: the state field changing length only invalidates the **cache**
position (`navigateToCache3` scans the state field to its separator, so the cache must sit right after it).  Rather than
physically shift the simulated tape (which would need a marker-aware ternary shift), we simply **re-place the cache**: after
writing the new state field (`clearStateFieldHome3`, entry 448, windowed), `cacheRefreshHome3` (entry 444) reads the current
symbol from the head marker and writes it at the *new* cache cell `home+1+newlen+1`.  The old cache cell is left as harmless
gap (the matcher never looks there; the simulated tape is found via the marker seek, not by contiguity).

So both tape-shift directions (entries 451–453) — genuine reusable machinery — turn out **unnecessary** for the state
update; the re-placement does the job with bit primitives only.

## What is proved (clean axioms, no `sorry`)

* **`stateUpdateFull3 <state-update states> mid2 <cache states>`** — `clearStateFieldHome3 … mid2 ++ cacheRefreshHome3 mid2
  …`.
* **`stateUpdateFull3_run`** (PROVED) — with the home marker, the head marker at `hm` beyond the rule region, no other
  marker in `(home, hm)`, the old/new (rule) state fields, the current cell a bit, and bounds: the config state field
  becomes the rule's new state and the cache is re-placed at the new boundary with the current symbol; head returns home.

## Honest scope

This is the **full state update** (state field + cache re-placement), handling the length change.  It does **not** connect
to the matched rule / `EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction,
**not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateFull

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk (clearBlock)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft (copyBlockLeft)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateHome (clearStateFieldHome3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateWindowed (clearStateFieldHome3_runW)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefreshHome (cacheRefreshHome3 cacheRefreshHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent (clearBlock_getD_outside clearBlock_getD_inside)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShift
  (copyBlockLeft_getD_outside_gen copyBlockLeft_getD_inside_gen)
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

/-- **The full state update.**  Write the new state field, then re-place the cache at the new boundary. -/
def stateUpdateFull3 (s sMid found cont mid d' sDone L1 L2 rf rc mid2
    sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf2 rc2 rout : ℕ) : TMachine3 :=
  clearStateFieldHome3 s sMid found cont mid d' sDone L1 L2 rf rc mid2 ++
    cacheRefreshHome3 mid2 sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf2 rc2 rout

/-- **The full state-update run (PROVED).**  Replaces the config state field with the rule's new state and re-places the
cache at the new boundary; head returns to the config home. -/
theorem stateUpdateFull3_run (s sMid found cont mid d' sDone L1 L2 rf rc mid2
    sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf2 rc2 rout
    home hm oldlen newlen : ℕ) (tp : List Sym3)
    (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD hm Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < hm → tp.getD j Sym3.O ≠ Sym3.M)
    (hd' : 1 ≤ d') (hdold : oldlen < d') (hnd : newlen < d') (hL1 : oldlen < L1) (hL2 : newlen < L2)
    (hgap : home + 1 + d' + newlen < hm)
    (hcold : ∀ i, i < oldlen → tp.getD (home + 1 + i) Sym3.O = Sym3.I)
    (hcoldsep : tp.getD (home + 1 + oldlen) Sym3.O = Sym3.O)
    (hcnew : ∀ i, i < newlen → tp.getD (home + 1 + d' + i) Sym3.O = Sym3.I)
    (hcnewsep : tp.getD (home + 1 + d' + newlen) Sym3.O = Sym3.O)
    (hcur : tp.getD (hm + 1) Sym3.O = Sym3.O ∨ tp.getD (hm + 1) Sym3.O = Sym3.I) (hbnd : hm + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (stateUpdateFull3 s sMid found cont mid d' sDone L1 L2 rf rc mid2
        sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf2 rc2 rout)) N (s, home + 1, tp)
      (rout, home + 1, writeAt3 (copyBlockLeft (clearBlock tp (home + 1) oldlen) (home + 1 + d') d' newlen)
        (home + 1 + newlen + 1) (tp.getD (hm + 1) Sym3.O)) := by
  obtain ⟨N1, h1⟩ := clearStateFieldHome3_runW s sMid found cont mid d' sDone L1 L2 rf rc mid2 home oldlen newlen tp
    hmarkHome (fun j hj1 hj2 => hclean j hj1 (by omega)) hd' hdold hnd hL1 hL2 (by omega) hcold hcoldsep hcnew hcnewsep
  set CB := clearBlock tp (home + 1) oldlen with hCB
  set RT := copyBlockLeft CB (home + 1 + d') d' newlen with hRT
  have hCBlen : CB.length = tp.length := clearBlock_length tp (home + 1) oldlen (by omega)
  have hRTlen : RT.length = tp.length := by
    rw [hRT, copyBlockLeft_length CB (home + 1 + d') d' newlen (by rw [hCBlen]; omega) (by omega)]; exact hCBlen
  -- a cell outside [home+1, home+1+newlen] reads the cleared-then-original value
  have hRT_far : ∀ j, home + 1 + newlen < j → home + 1 + oldlen ≤ j → RT.getD j Sym3.O = tp.getD j Sym3.O := by
    intro j hj1 hj2
    rw [hRT, copyBlockLeft_getD_outside_gen CB (home + 1 + d') d' newlen j (by omega) (Or.inr (by omega)), hCB,
      clearBlock_getD_outside tp (home + 1) oldlen j (Or.inr (by omega))]
  -- no marker in (home, hm) on RT
  have hRT_noM : ∀ j, home < j → j < hm → RT.getD j Sym3.O ≠ Sym3.M := by
    intro j hj1 hj2
    rcases Nat.lt_or_ge j (home + 1 + newlen + 1) with hin | hout
    · rw [hRT, copyBlockLeft_getD_inside_gen CB (home + 1 + d') d' newlen j (by omega) (by omega) (by omega), hCB,
        clearBlock_getD_outside tp (home + 1) oldlen (j + d') (Or.inr (by omega)),
        show j + d' = home + 1 + d' + (j - (home + 1)) from by omega]
      rcases Nat.lt_or_ge (j - (home + 1)) newlen with hlt | hge
      · rw [hcnew (j - (home + 1)) hlt]; decide
      · rw [show j - (home + 1) = newlen from by omega, hcnewsep]; decide
    · rw [hRT, copyBlockLeft_getD_outside_gen CB (home + 1 + d') d' newlen j (by omega) (Or.inr (by omega)), hCB]
      rcases Nat.lt_or_ge j (home + 1 + oldlen) with hcl | hncl
      · rw [clearBlock_getD_inside tp (home + 1) oldlen j (by omega) hcl]; decide
      · rw [clearBlock_getD_outside tp (home + 1) oldlen j (Or.inr hncl)]; exact hclean j hj1 hj2
  -- cells of the new state field read the rule field
  have hRT_state : ∀ i, i < newlen → RT.getD (home + 1 + i) Sym3.O = Sym3.I := by
    intro i hi
    rw [hRT, copyBlockLeft_getD_inside_gen CB (home + 1 + d') d' newlen (home + 1 + i) (by omega) (by omega) (by omega),
      hCB, clearBlock_getD_outside tp (home + 1) oldlen (home + 1 + i + d') (Or.inr (by omega)),
      show home + 1 + i + d' = home + 1 + d' + i from by omega]
    exact hcnew i hi
  have hRT_statesep : RT.getD (home + 1 + newlen) Sym3.O = Sym3.O := by
    rw [hRT, copyBlockLeft_getD_inside_gen CB (home + 1 + d') d' newlen (home + 1 + newlen) (by omega) (by omega) (by omega),
      hCB, clearBlock_getD_outside tp (home + 1) oldlen (home + 1 + newlen + d') (Or.inr (by omega)),
      show home + 1 + newlen + d' = home + 1 + d' + newlen from by omega]
    exact hcnewsep
  -- assemble the cache-refresh hypotheses (d = hm - (home+1), a = newlen)
  have hmark_cr : RT.getD ((home + 1) + (hm - (home + 1))) Sym3.O = Sym3.M := by
    rw [show (home + 1) + (hm - (home + 1)) = hm from by omega, hRT_far hm (by omega) (by omega)]; exact hmarkHead
  have hcur_cr : RT.getD ((home + 1) + (hm - (home + 1)) + 1) Sym3.O = Sym3.O ∨
      RT.getD ((home + 1) + (hm - (home + 1)) + 1) Sym3.O = Sym3.I := by
    rw [show (home + 1) + (hm - (home + 1)) + 1 = hm + 1 from by omega, hRT_far (hm + 1) (by omega) (by omega)]; exact hcur
  have hmarkHome_cr : RT.getD home Sym3.O = Sym3.M := by
    rw [hRT, copyBlockLeft_getD_outside_gen CB (home + 1 + d') d' newlen home (by omega) (Or.inl (by omega)), hCB,
      clearBlock_getD_outside tp (home + 1) oldlen home (Or.inl (by omega))]; exact hmarkHome
  obtain ⟨N2, h2⟩ := cacheRefreshHome3_run mid2 sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW
    sFin rf2 rc2 rout (hm - (home + 1)) home newlen RT hmark_cr
    (fun k hk => hRT_noM ((home + 1) + k) (by omega) (by omega))
    (by rw [hRTlen]; omega) (by rw [hRTlen]; omega) hcur_cr hmarkHome_cr
    (fun k hk0 hk => hRT_noM (home + k) (by omega) (by omega)) hRT_state hRT_statesep (by rw [hRTlen]; omega)
    (by rw [hRTlen]; omega)
  rw [show (home + 1) + (hm - (home + 1)) + 1 = hm + 1 from by omega, hRT_far (hm + 1) (by omega) (by omega)] at h2
  exact ⟨N1 + N2, reachIn_seq3 (clearStateFieldHome3 s sMid found cont mid d' sDone L1 L2 rf rc mid2)
    (cacheRefreshHome3 mid2 sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf2 rc2 rout)
    N1 N2 _ _ _ h1 h2⟩

/-!
**The full state update, proved.**  `stateUpdateFull3` replaces the config state field with the rule's new state and
re-places the cache at the new boundary — handling the length change without shifting the marker-containing simulated tape.
Next: the matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateFull

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateFull.stateUpdateFull3_run

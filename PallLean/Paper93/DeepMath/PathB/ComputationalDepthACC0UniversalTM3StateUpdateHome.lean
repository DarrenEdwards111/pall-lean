import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3StateUpdate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyContent
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ClearContent
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome

/-!
# Entry 446 — universal-TM-table build: the home-to-home state update `clearStateFieldHome3` (proved)

The state update (`clearStateField3`, entry 430) replaces the config's state field but ends deep in the rule region.  This
brick makes it **home-to-home**: append a reset (`resetToHome3`, 408) back to the config home.  The crux is re-establishing
the marker invariant on the transformed tape `copyBlockLeft (clearBlock tp (home+1) oldlen) (home+1+d') d' newlen` — which
uses the copier content (entry 445, disjoint case `newlen < d'`) and the clearer content (entry 429): the cleared cells are
`O`, the copied destination holds the rule field (`I`s/`O`), and everything else is preserved, so the reset window has no
marker.

## What is proved (clean axioms, no `sorry`)

* **`clearStateFieldHome3 <state-update states> rf rc rout`** — `clearStateField3 … ++ resetToHome3 sDone rf rc rout`.
* **`clearStateFieldHome3_run`** (PROVED) — from the config home, with a single home marker, `oldlen < d'`, `newlen < d'`,
  budgets, bounds, the old field and the rule field: `∃ N, reachIn N (s, home+1, tp) (rout, home+1, copyBlockLeft
  (clearBlock tp (home+1) oldlen) (home+1+d') d' newlen)` — the config state field is replaced by the rule's new state and
  the head returns to the config home.

## Honest scope

This is the **home-to-home state update** — one apply phase with a canonical endpoint.  It does **not** assemble
`EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk (clearBlock)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft (copyBlockLeft)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdate (clearStateField3 clearStateField3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyContent (copyBlockLeft_getD_outside copyBlockLeft_getD_inside)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent (clearBlock_getD_outside clearBlock_getD_inside)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (w : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

/-- The clearer preserves length (in bounds). -/
private theorem clearBlock_length (tp : List Sym3) (h m : ℕ) (hb : h + m ≤ tp.length) :
    (clearBlock tp h m).length = tp.length := by
  induction m generalizing h tp with
  | zero => rfl
  | succ m ih =>
      show (clearBlock (writeAt3 tp h Sym3.O) (h + 1) m).length = tp.length
      rw [ih (writeAt3 tp h Sym3.O) (h + 1) (by rw [writeAt3_length_eq tp h Sym3.O (by omega)]; omega),
        writeAt3_length_eq tp h Sym3.O (by omega)]

/-- The leftward copier preserves length (in bounds). -/
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

/-- **The home-to-home state update.**  Update the state field, then reset to the config home. -/
def clearStateFieldHome3 (s sMid found cont mid d' sDone L1 L2 rf rc rout : ℕ) : TMachine3 :=
  clearStateField3 s sMid found cont mid d' sDone L1 L2 ++ resetToHome3 sDone rf rc rout

/-- **The home-to-home state-update run (PROVED).**  Replaces the config state field with the rule's new state and returns
the head to the config home. -/
theorem clearStateFieldHome3_run (s sMid found cont mid d' sDone L1 L2 rf rc rout home oldlen newlen : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M) (hclean : ∀ j, j ≠ home → tp.getD j Sym3.O ≠ Sym3.M)
    (hd' : 1 ≤ d') (hdold : oldlen < d') (hnd : newlen < d') (hL1 : oldlen < L1) (hL2 : newlen < L2)
    (hbnd : home + 1 + d' + newlen < tp.length)
    (hcold : ∀ i, i < oldlen → tp.getD (home + 1 + i) Sym3.O = Sym3.I)
    (hcoldsep : tp.getD (home + 1 + oldlen) Sym3.O = Sym3.O)
    (hcnew : ∀ i, i < newlen → tp.getD (home + 1 + d' + i) Sym3.O = Sym3.I)
    (hcnewsep : tp.getD (home + 1 + d' + newlen) Sym3.O = Sym3.O) :
    ∃ N, reachIn (toNTM3 (clearStateFieldHome3 s sMid found cont mid d' sDone L1 L2 rf rc rout)) N (s, home + 1, tp)
      (rout, home + 1, copyBlockLeft (clearBlock tp (home + 1) oldlen) (home + 1 + d') d' newlen) := by
  obtain ⟨N1, h1⟩ := clearStateField3_run s sMid found cont mid d' sDone L1 L2 home oldlen newlen tp hmark hclean hd'
    hdold hL1 hL2 hbnd hcold hcoldsep hcnew hcnewsep
  set CB := clearBlock tp (home + 1) oldlen with hCB
  set RT := copyBlockLeft CB (home + 1 + d') d' newlen with hRT
  have hCBlen : CB.length = tp.length := clearBlock_length tp (home + 1) oldlen (by omega)
  have hRTlen : RT.length = tp.length := by rw [hRT]; rw [copyBlockLeft_length CB (home + 1 + d') d' newlen (by rw [hCBlen]; omega) (by omega)]; exact hCBlen
  -- home marker survives
  have hmark_r : RT.getD home Sym3.O = Sym3.M := by
    rw [hRT, copyBlockLeft_getD_outside CB (home + 1 + d') d' newlen home hnd (by omega) (Or.inl (by omega)),
      hCB, clearBlock_getD_outside tp (home + 1) oldlen home (Or.inl (by omega))]
    exact hmark
  -- no marker in the reset window
  have hno_r : ∀ k, 0 < k → k ≤ d' + newlen + 1 → RT.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    rcases Nat.lt_or_ge (home + k) (home + 1 + newlen + 1) with hAdest | hBout
    · -- destination region [home+1, home+1+newlen]: copied rule field
      rw [hRT, copyBlockLeft_getD_inside CB (home + 1 + d') d' newlen (home + k) hnd (by omega) (by omega) (by omega),
        hCB, clearBlock_getD_outside tp (home + 1) oldlen (home + k + d') (Or.inr (by omega))]
      have hi : home + k + d' = home + 1 + d' + (k - 1) := by omega
      rw [hi]
      rcases Nat.lt_or_ge (k - 1) newlen with hin | hge
      · rw [hcnew (k - 1) hin]; decide
      · rw [show k - 1 = newlen from by omega, hcnewsep]; decide
    · -- outside the destination: cleared `O` or original (marker-free by hclean)
      rw [hRT, copyBlockLeft_getD_outside CB (home + 1 + d') d' newlen (home + k) hnd (by omega) (Or.inr (by omega)), hCB]
      rcases Nat.lt_or_ge (home + k) (home + 1 + oldlen) with hcl | hncl
      · rw [clearBlock_getD_inside tp (home + 1) oldlen (home + k) (by omega) hcl]; decide
      · rw [clearBlock_getD_outside tp (home + 1) oldlen (home + k) (Or.inr hncl)]
        exact hclean (home + k) (by omega)
  obtain ⟨N2, h2⟩ := resetToHome3_run sDone rf rc rout home (d' + newlen + 1) RT hmark_r hno_r (by rw [hRTlen]; omega)
  rw [show home + (d' + newlen + 1) = home + 1 + d' + newlen from by omega] at h2
  exact ⟨N1 + N2, reachIn_seq3 (clearStateField3 s sMid found cont mid d' sDone L1 L2)
    (resetToHome3 sDone rf rc rout) N1 N2 _ _ _ h1 h2⟩

/-!
**The home-to-home state update, proved.**  `clearStateFieldHome3` replaces the config state field and returns the head to
the config home, re-establishing the marker invariant via the copier and clearer content.  Next: the master apply sequence
(state update + symbol write + move + cache refresh, all home-to-home) and the matcher↔lookup correspondence toward
`EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdateHome.clearStateFieldHome3_run

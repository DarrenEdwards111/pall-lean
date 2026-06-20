import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Transfer
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ClearContent

/-!
# Entry 430 — universal-TM-table build: the state-field update `clearStateField3` (proved)

This assembles the complete simulated-**state** update of the apply phase: replace the configuration's old state field with
the matched rule's new-state field, *handling the length change*.  It clears the old field first (`walkRightClearField3`,
entry 418) and then transfers the new one (`transferFieldLeft3`, entry 428).

The two phases run on *different* tapes (the transfer runs on the cleared tape), so the cross-tape hypotheses are
discharged with the clearer-content lemmas (entry 429): the home marker and the distant rule field survive clearing the
config field (`clearBlock_getD_outside`), and the cells of the cleared field read `O` (`clearBlock_getD_inside`), so no
marker is in the reset window.  This is why clearing first is safe — the rule field, far to the right (`d' > oldlen`), is
untouched.

## What is proved (clean axioms, no `sorry`)

* **`clearStateField3 s sMid found cont mid d' sDone L1 L2`** — `walkRightClearField3 s sMid L1 ++ transferFieldLeft3 sMid
  found cont mid d' sDone L2`.
* **`clearStateField3_run`** (PROVED) — with a home marker at `home`, no marker elsewhere, `oldlen < d'`, budgets, bounds,
  the old config field (`oldlen` ones then `O` at `home+1`) and the rule field (`newlen` ones then `O` at `home+1+d'`):
  `∃ N, reachIn N (s, home+1, tp) (sDone, home+1+d'+newlen, copyBlockLeft (clearBlock tp (home+1) oldlen) (home+1+d') d'
  newlen)` — the config's state field is cleared and replaced by a copy of the rule's new-state field.

## Honest scope

This is the **state-field update** (clear + transfer), the last per-step *transformation*.  It does **not** yet sequence
lookup → apply → state-update into one step, nor assemble `EmitsEncodedStep3`.  Building those fragment by fragment is the
genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdate

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk (walkRightClearField3 walkRightClearField3_run clearBlock)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent (clearBlock_getD_outside clearBlock_getD_inside)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Transfer (transferFieldLeft3 transferFieldLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft (copyBlockLeft)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- The clearer preserves length (in bounds). -/
private theorem clearBlock_length (tp : List Sym3) (h m : ℕ) (hb : h + m ≤ tp.length) :
    (clearBlock tp h m).length = tp.length := by
  induction m generalizing h tp with
  | zero => rfl
  | succ m ih =>
      show (clearBlock (writeAt3 tp h Sym3.O) (h + 1) m).length = tp.length
      rw [ih (writeAt3 tp h Sym3.O) (h + 1) (by rw [writeAt3_length_eq tp h Sym3.O (by omega)]; omega),
        writeAt3_length_eq tp h Sym3.O (by omega)]

/-- **The state-field update.**  Clear the old config field, then transfer the rule's new-state field in. -/
def clearStateField3 (s sMid found cont mid d' sDone L1 L2 : ℕ) : TMachine3 :=
  walkRightClearField3 s sMid L1 ++ transferFieldLeft3 sMid found cont mid d' sDone L2

/-- **The state-field update run (PROVED).**  Replaces the config state field with a copy of the rule's new-state field. -/
theorem clearStateField3_run (s sMid found cont mid d' sDone L1 L2 home oldlen newlen : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M) (hclean : ∀ j, j ≠ home → tp.getD j Sym3.O ≠ Sym3.M)
    (hd' : 1 ≤ d') (hdold : oldlen < d') (hL1 : oldlen < L1) (hL2 : newlen < L2)
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
    · rw [htp', clearBlock_getD_outside tp (home + 1) oldlen (home + k) (Or.inr hge)]
      exact hclean (home + k) (by omega)
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

/-!
**The state-field update, proved.**  `clearStateField3` clears the old config state field and copies in the rule's
new-state field, handling the length change, with the rule field surviving via the clearer-content lemmas.  Next: sequence
lookup → apply-tape-step → state-update into one simulated step, and assemble `EmitsEncodedStep3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3StateUpdate.clearStateField3_run

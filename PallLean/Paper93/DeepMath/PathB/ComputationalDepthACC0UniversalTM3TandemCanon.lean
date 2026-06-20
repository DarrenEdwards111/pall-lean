import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CursTape

/-!
# Entry 479 — generic scan loop: one canonical tandem step `tandemStepCanon_run` (proved)

One full tandem iteration (`tandemStep3`, entry 476) maps the canonical comparison tape (`cursTape`, entry 478) at step `i`
to the same form at step `i+1`: both cursors advance by one.  The tape after the step is a six-layer `writeAt3` expression;
we prove it *equals* `cursTape … (i+1)` by extensionality (`List.ext_getElem`, comparing `getD` cell-by-cell via
`writeAt3_getD`) — robust where the nested-`rw` normalization was fragile.

## What is proved (clean axioms, no `sorry`)

* **`tandemStepCanon_run`** (PROVED) — base tape's field cells `I`, gap marker-free, in bounds: `∃ N, reachIn N (s, cp+i,
  cursTape tp cp g i) (lcrFound, cp+i+1, cursTape tp cp g (i+1))` — one tandem step advances the canonical form.

## Honest scope

This is **one canonical tandem step**.  It does **not** yet iterate it (induction on the step count), nor build the
four-way end-branch, the symbol compare, the match-or-advance branch, the generic apply, nor a fixed `U` /
`EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemCanon

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3 toNTM3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemStep (tandemStep3 tandemStep3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg (writeAt3_eq_set)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape
  (cursTape cursTape_length cursTape_cursorL cursTape_cursorR cursTape_other)

private theorem wlen (t : List Sym3) (p : ℕ) (w : Sym3) (hp : p < t.length) :
    (writeAt3 t p w).length = t.length := by
  rw [writeAt3_eq_set t p w hp, List.length_set]

/-- **One canonical tandem step advances the comparison (PROVED).** -/
theorem tandemStepCanon_run (s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrFound lcrCont : ℕ)
    (tp : List Sym3) (cp g i : ℕ) (hg : 2 ≤ g)
    (hfC : tp.getD (cp + i) Sym3.O = Sym3.I) (hfC1 : tp.getD (cp + i + 1) Sym3.O = Sym3.I)
    (hfR : tp.getD (cp + g + i) Sym3.O = Sym3.I) (hfR1 : tp.getD (cp + g + i + 1) Sym3.O = Sym3.I)
    (hgap : ∀ j, cp + i < j → j < cp + g + i → tp.getD j Sym3.O ≠ Sym3.M) (hbound : cp + g + i + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (tandemStep3 s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrFound lcrCont)) N
      (s, cp + i, cursTape tp cp g i) (lcrFound, cp + i + 1, cursTape tp cp g (i + 1)) := by
  have hclen : (cursTape tp cp g i).length = tp.length := cursTape_length tp cp g i (by omega) (by omega)
  obtain ⟨N, hrun⟩ := tandemStep3_run s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrFound lcrCont
    (cursTape tp cp g i) (cp + i) g hg
    (cursTape_cursorL tp cp g i (by omega))
    (by rw [cursTape_other tp cp g i _ (by omega) (by omega)]; exact hfC1)
    (by rw [show cp + i + g = cp + g + i from by omega]; exact cursTape_cursorR tp cp g i)
    (by rw [show cp + i + g + 1 = cp + g + i + 1 from by omega,
          cursTape_other tp cp g i _ (by omega) (by omega)]; exact hfR1)
    (fun j hj1 hj2 => by
      rw [cursTape_other tp cp g i _ (by omega) (by omega)]; exact hgap j (by omega) (by omega))
    (by rw [hclen, show cp + i + g + 1 = cp + g + i + 1 from by omega]; exact hbound)
  refine ⟨N, ?_⟩
  -- the post-step tape equals the canonical form at i+1
  have key : writeAt3 (writeAt3 (writeAt3 (writeAt3 (cursTape tp cp g i) (cp + i) Sym3.I) (cp + i + 1) Sym3.M)
        (cp + i + g) Sym3.I) (cp + i + g + 1) Sym3.M = cursTape tp cp g (i + 1) := by
    rw [show cp + i + g = cp + g + i from by omega]
    have hci : (cursTape tp cp g i).length = tp.length := hclen
    have l1 : (writeAt3 (cursTape tp cp g i) (cp + i) Sym3.I).length = tp.length := by
      rw [wlen _ _ _ (by rw [hci]; omega), hci]
    have l2 : (writeAt3 (writeAt3 (cursTape tp cp g i) (cp + i) Sym3.I) (cp + i + 1) Sym3.M).length = tp.length := by
      rw [wlen _ _ _ (by rw [l1]; omega), l1]
    have l3 : (writeAt3 (writeAt3 (writeAt3 (cursTape tp cp g i) (cp + i) Sym3.I) (cp + i + 1) Sym3.M)
        (cp + g + i) Sym3.I).length = tp.length := by rw [wlen _ _ _ (by rw [l2]; omega), l2]
    apply List.ext_getElem
    · rw [wlen _ _ _ (by rw [l3]; omega), l3, cursTape_length tp cp g (i + 1) (by omega) (by omega)]
    · intro n h1 h2
      rw [← List.getD_eq_getElem (d := Sym3.O) _ h1, ← List.getD_eq_getElem (d := Sym3.O) _ h2]
      simp only [cursTape, writeAt3_getD]
      split_ifs <;> simp_all <;> omega
  rw [← key]
  exact hrun

/-!
**One canonical tandem step, proved.**  `tandemStepCanon_run` advances `cursTape` by one (the post-step tape shown equal to
the canonical `i+1` form by `getD`-extensionality).  Next: iterate it (induction on the step count) to walk both cursors to
the field ends, then the four-way end-branch — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemCanon

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemCanon.tandemStepCanon_run

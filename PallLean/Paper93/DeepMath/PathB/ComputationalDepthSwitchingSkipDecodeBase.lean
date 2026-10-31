import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipDecode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MaintainInvariant
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StreamRecursion

/-!
# Tight switching, skip-encoded decoder step 5: the base-relative decoder (branch `razborov-recoverRho-wip`)

The base-relative generalisation of the multi-step decoder (skip-decoder step 4).  Brick 144 ran `skipDecode`
with the running state threaded as the descent state `σ` itself.  Here the running state is an arbitrary
**sub-restriction base** `τ ⊑ σ` (`SubRestriction τ σ`), falsification-agreeing with `σ`, threaded forward by
reading values off the leaf — the form the `(4w)^s` injection needs (the inverse map starts from a base
recovered from `σ_end`, not from the unknown bad restriction).

```
  SubRestriction τ σ → (∀ U ∈ cs, termFalsified τ U = termFalsified σ U) →
    skipDecode cs (deepestEnd cs F σ) (deepestSkipSeq cs F σ) (activeTerm cs τ) τ = deepestSel cs F σ.
```

The advance bit is what makes the active-term threading work from a *different* state than the descent:

* On a **persist** step the decoder keeps the current term — *no* recomputation, so falsification-agreement is
  **not used here at all** (the kept term equals the descent's by brick 143, a fact about `σ` alone).
* Only on an **advance** step does it recompute `activeTerm cs τ'`, and *there* falsification-agreement is used
  (`activeTerm_eq_of_falsified_agree`) to match the descent's new active term.

So agreement is consumed at advance steps only — in `recoverStream` it is consumed at *every* step.

* `skipDecode_deepestSkipSeq_base` — `skipDecode` recovers `deepestSel` from any falsification-agreeing
  sub-restriction base.

## Honest scope

This is the base-relative recovery **under the falsification-agreement invariant** (`SubRestriction` +
agreement + the canonical structure) — the same invariant `recoverStream` carries.  The advance bit
demonstrably localises *where* agreement is used (advance steps only, never persist steps), but the theorem
still **assumes** agreement, so instantiating it at a concrete base (e.g. the all-free state) still needs that
agreement — which for the all-free base is exactly `hnf`.  **Dropping** the agreement hypothesis — supplying
the advance-step active term from the leaf `σ_end` instead, the genuine empty-skip wall — is **not** done here;
this delivers the base-relative decoder and pins the agreement use to advance steps.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The base-relative multi-step decoder recovers `deepestSel`.**  From any sub-restriction base `τ ⊑ σ`
falsification-agreeing with `σ`, the advance-bit-driven decoder (active term initialised to `activeTerm cs τ`,
threaded by the advance bit) recovers the deepest selected set.  Agreement is used only at advance steps. -/
theorem skipDecode_deepestSkipSeq_base (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ τ : Fin n → Option Bool),
      SubRestriction τ σ →
      (∀ U ∈ cs, SwitchingCounting.termFalsified τ U = SwitchingCounting.termFalsified σ U) →
      skipDecode cs (deepestEnd cs F σ) (deepestSkipSeq cs F σ) (SwitchingCounting.activeTerm cs τ) τ
        = deepestSel cs F σ := by
  intro F
  induction F with
  | zero => intro σ τ _ _; rfl
  | succ F ih =>
    intro σ τ hsub hagree
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      rw [deepestSkipSeq_anyTermSat cs (F + 1) σ hany, deepestSel_anyTermSat cs (F + 1) σ hany, skipDecode]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [show deepestSkipSeq cs (F + 1) σ = [] by rw [deepestSkipSeq]; simp [hany, hact],
            show deepestSel cs (F + 1) σ = ∅ by rw [deepestSel]; simp [hany, hact], skipDecode]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [show deepestSkipSeq cs (F + 1) σ = [] by rw [deepestSkipSeq]; simp [hany, hact, hh],
              show deepestSel cs (F + 1) σ = ∅ by rw [deepestSel]; simp [hany, hact, hh], skipDecode]
        | some ℓ =>
          have hτany : SwitchingCounting.anyTermSat cs τ = false := anyTermSat_false_of_sub hsub hany
          have hactτ : SwitchingCounting.activeTerm cs τ = some T := by
            rw [activeTerm_eq_of_falsified_agree hagree hτany hany]; exact hact
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hcla : clauseLitAt T (pivotPosOf cs σ) = some ℓ := by
            rw [clauseLitAt_pivotPosOf hact (by rw [hatl]; rfl)]; exact hatl
          set σ' : Fin n → Option Bool := deepestStep cs F σ with hσ'
          set adv : Bool := SwitchingCounting.termFalsified σ' T ||
            decide ((SwitchingCounting.freeLits σ' T).length = 0) with hadv
          have hstep : deepestStep cs F σ =
              (if (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                  (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
               then fixVar σ (litVar ℓ) false else fixVar σ (litVar ℓ) true) :=
            deepestStep_active cs F σ T hany hact hh
          have hσv : σ (litVar ℓ) = none := by
            have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
            have hfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hmem).2
            rw [litFree_var] at hfree; exact Option.isNone_iff_eq_none.mp hfree
          have hτv : τ (litVar ℓ) = none := sub_free hsub hσv
          obtain ⟨b, hbval⟩ := deepestStep_active_fixes cs F σ T ℓ hany hact hh
          have hev : deepestEnd cs (F + 1) σ (litVar ℓ) = some b := by
            rw [deepestEnd_active_var_eq cs F σ T ℓ hany hact hh]; exact hbval
          have hσ'b : σ' = fixVar σ (litVar ℓ) b := by
            rw [hσ', hstep]
            by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                          (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
            · rw [if_pos hd]; congr 1
              have := hbval; rw [hstep, if_pos hd, fixVar, Function.update_self, Option.some_inj] at this
              exact this
            · rw [if_neg hd]; congr 1
              have := hbval; rw [hstep, if_neg hd, fixVar, Function.update_self, Option.some_inj] at this
              exact this
          have hseq : deepestSkipSeq cs (F + 1) σ
              = (pivotPosOf cs σ, !SwitchingCounting.litFalse σ' ℓ, adv) :: deepestSkipSeq cs F σ' := by
            rw [deepestSkipSeq]
            by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                          (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
            · have hb : fixVar σ (litVar ℓ) false = σ' := by rw [hσ', hstep, if_pos hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd]; rw [hb, hadv]
            · have hb : fixVar σ (litVar ℓ) true = σ' := by rw [hσ', hstep, if_neg hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd]; rw [hb, hadv]
          have hsel : deepestSel cs (F + 1) σ = insert (litVar ℓ) (deepestSel cs F σ') := by
            rw [deepestSel]
            by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                          (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
            · have hb : fixVar σ (litVar ℓ) false = σ' := by rw [hσ', hstep, if_pos hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd]; rw [hb]
            · have hb : fixVar σ (litVar ℓ) true = σ' := by rw [hσ', hstep, if_neg hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd]; rw [hb]
          have hend : deepestEnd cs (F + 1) σ = deepestEnd cs F σ' := by rw [deepestEnd_succ, hσ']
          have hτ'eq : fixVar τ (litVar ℓ) ((deepestEnd cs (F + 1) σ (litVar ℓ)).getD false)
              = fixVar τ (litVar ℓ) b := by rw [hev, Option.getD_some]
          rw [hseq, hsel, hactτ, skipDecode]
          simp only [hcla, hτ'eq]
          refine congrArg (insert (litVar ℓ)) ?_
          rw [hend]
          cases hany' : SwitchingCounting.anyTermSat cs σ' with
          | true =>
            rw [deepestSkipSeq_anyTermSat cs F σ' hany', deepestSel_anyTermSat cs F σ' hany', skipDecode]
          | false =>
            have hsubτ' : SubRestriction (fixVar τ (litVar ℓ) b) σ' := by
              rw [hσ'b]; exact subRestriction_fixVar hsub
            have hagreeτ' : ∀ U ∈ cs,
                SwitchingCounting.termFalsified (fixVar τ (litVar ℓ) b) U
                  = SwitchingCounting.termFalsified σ' U := by
              rw [hσ'b]; exact maintain_falsified_agree hτv hσv hagree
            have hτany' : SwitchingCounting.anyTermSat cs (fixVar τ (litVar ℓ) b) = false :=
              anyTermSat_false_of_sub hsubτ' hany'
            have hnextT : (if adv then SwitchingCounting.activeTerm cs (fixVar τ (litVar ℓ) b)
                else some T) = SwitchingCounting.activeTerm cs (fixVar τ (litVar ℓ) b) := by
              by_cases hadvv : adv = true
              · rw [if_pos hadvv]
              · rw [if_neg hadvv]
                symm
                rw [activeTerm_eq_of_falsified_agree hagreeτ' hτany' hany', hσ'b]
                have hbitfalse : (SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) T ||
                    decide ((SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) T).length = 0)) = false := by
                  have hadvf : adv = false := by cases hh2 : adv <;> simp_all
                  rw [hadv, hσ'b] at hadvf; exact hadvf
                have hany'' : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false := by
                  rw [← hσ'b]; exact hany'
                exact (advanceBit_false_iff_active_persists hact hh hany'').mp hbitfalse
            rw [hnextT]
            exact ih σ' (fixVar τ (litVar ℓ) b) hsubτ' hagreeτ'

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.skipDecode_deepestSkipSeq_base

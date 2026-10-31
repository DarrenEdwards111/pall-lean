import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipSemantics
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverStreamCorrect

/-!
# Tight switching, skip-encoded decoder step 4: the multi-step advance-bit decoder (branch `razborov-recoverRho-wip`)

The multi-step assembly of the per-step advance-bit semantics (skip-decoder step 3).  `recoverStream` recovers
the active-clause stream by **recomputing** `activeTerm cs τ` at *every* step — which requires the
falsification-agreement invariant (`activeTerm_eq_of_falsified_agree`), the single place `hnf` is consumed.

`skipDecode` instead **threads the active term explicitly** and consults the advance bit: on a *persist* step
(bit `false`) it keeps the current term `T` — no recomputation, hence no agreement needed there — and only on
an *advance* step (bit `true`) does it re-scan.  Brick 143 (`advanceBit_false_iff_active_persists`) is exactly
what justifies keeping `T`: bit `false` ⟺ `activeTerm cs σ' = some T`.

We prove the decoder reproduces the selected set:

```
  activeTerm cs σ = T₀  →  skipDecode cs (deepestEnd cs F σ) (deepestSkipSeq cs F σ) T₀ σ = deepestSel cs F σ.
```

The running state is threaded as the descent state (`τ = σ`, kept in sync because the value read off the leaf
`deepestEnd cs F σ (litVar ℓ)` is exactly the branch value `deepestStep` fixed, via
`deepestEnd_active_var_eq`); the active-term accumulator is threaded through the whole path by the advance bit.

* `skipDecode` — the multi-step decoder: explicit active-term accumulator, advance-bit-driven (persist = keep,
  advance = re-scan), reading values off the leaf.
* `skipDecode_deepestSkipSeq` — it recovers `deepestSel` along the canonical path.

## Honest scope

This is the **soundness of the decoder's recursion**: the advance bit correctly threads the active term across
the whole multi-step path (persist steps need no agreement, by brick 143), and the recovered set is exactly
`deepestSel`.  The running state is threaded as the descent state `σ`.  Generalising the start from `σ` to a
sub-restriction base recovered from the leaf alone — i.e. the `recoverStream`-style `SubRestriction` argument
with the advance bit replacing falsification-agreement *at advance steps only* — is the final step toward the
fully `hnf`-free `(4w)^s` injection.  It is **not** done here; this establishes the decoder logic is correct.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The multi-step advance-bit decoder.**  Threads the active term `curT` and the running state `τ`: read
the literal at the recorded position of the current term, fix its variable to the leaf value, and update the
active term by the advance bit — keep `curT` on a persist step (bit `false`), re-scan `activeTerm cs τ'` on an
advance step (bit `true`).  Recovers the selected-variable set. -/
def skipDecode (cs : List (Clause n)) (σ_end : Fin n → Option Bool) :
    List (ℕ × Bool × Bool) → Option (Clause n) → (Fin n → Option Bool) → Finset (Fin n)
  | [], _, _ => ∅
  | _ :: _, none, _ => ∅
  | (p, _, adv) :: rest, some T, τ =>
      match clauseLitAt T p with
      | none => ∅
      | some ℓ =>
          insert (litVar ℓ)
            (skipDecode cs σ_end rest
              (if adv then
                  SwitchingCounting.activeTerm cs (fixVar τ (litVar ℓ) ((σ_end (litVar ℓ)).getD false))
                else some T)
              (fixVar τ (litVar ℓ) ((σ_end (litVar ℓ)).getD false)))

/-- At a satisfied leaf the skip-aware path is empty (any fuel). -/
theorem deepestSkipSeq_anyTermSat (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (h : SwitchingCounting.anyTermSat cs σ = true) : deepestSkipSeq cs F σ = [] := by
  cases F with
  | zero => rfl
  | succ F => rw [deepestSkipSeq]; simp [h]

/-- At a satisfied leaf the deepest selected set is empty (any fuel). -/
theorem deepestSel_anyTermSat (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (h : SwitchingCounting.anyTermSat cs σ = true) : deepestSel cs F σ = ∅ := by
  cases F with
  | zero => rfl
  | succ F => rw [deepestSel]; simp [h]

/-- **The decoder recovers `deepestSel` along the canonical path.**  With the active-term accumulator
initialised to the descent's active term, the advance-bit-driven decoder threads the active clause across the
whole path (persist steps justified by `advanceBit_false_iff_active_persists`) and recovers the deepest selected
set.  The running state is threaded as the descent state. -/
theorem skipDecode_deepestSkipSeq (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (T₀ : Option (Clause n)),
      SwitchingCounting.activeTerm cs σ = T₀ →
      skipDecode cs (deepestEnd cs F σ) (deepestSkipSeq cs F σ) T₀ σ = deepestSel cs F σ := by
  intro F
  induction F with
  | zero => intro σ T₀ _; rfl
  | succ F ih =>
    intro σ T₀ hT₀
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      rw [show deepestSkipSeq cs (F + 1) σ = [] by rw [deepestSkipSeq]; simp [hany],
          show deepestSel cs (F + 1) σ = ∅ by rw [deepestSel]; simp [hany], skipDecode]
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
          subst hT₀
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hcla : clauseLitAt T (pivotPosOf cs σ) = some ℓ := by
            rw [clauseLitAt_pivotPosOf hact (by rw [hatl]; rfl)]; exact hatl
          set σ' : Fin n → Option Bool := deepestStep cs F σ with hσ'
          -- the recorded advance bit at this step
          set adv : Bool := SwitchingCounting.termFalsified σ' T ||
            decide ((SwitchingCounting.freeLits σ' T).length = 0) with hadv
          -- the recorded branch equals the descent step `σ'`, in either depth case
          have hstep : deepestStep cs F σ =
              (if (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                  (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
               then fixVar σ (litVar ℓ) false else fixVar σ (litVar ℓ) true) :=
            deepestStep_active cs F σ T hany hact hh
          -- path / selected-set unfold to `σ'`
          have hseq : deepestSkipSeq cs (F + 1) σ
              = (pivotPosOf cs σ, !SwitchingCounting.litFalse σ' ℓ, adv) :: deepestSkipSeq cs F σ' := by
            rw [deepestSkipSeq]
            by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                          (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
            · have hb : fixVar σ (litVar ℓ) false = σ' := by rw [hσ', hstep, if_pos hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd]
              rw [hb, hadv]
            · have hb : fixVar σ (litVar ℓ) true = σ' := by rw [hσ', hstep, if_neg hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd]
              rw [hb, hadv]
          have hsel : deepestSel cs (F + 1) σ = insert (litVar ℓ) (deepestSel cs F σ') := by
            rw [deepestSel]
            by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                          (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
            · have hb : fixVar σ (litVar ℓ) false = σ' := by rw [hσ', hstep, if_pos hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd]; rw [hb]
            · have hb : fixVar σ (litVar ℓ) true = σ' := by rw [hσ', hstep, if_neg hd]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd]; rw [hb]
          -- the leaf value at `litVar ℓ` keeps the threaded state equal to `σ'`
          obtain ⟨b, hb⟩ := deepestStep_active_fixes cs F σ T ℓ hany hact hh
          have hev : deepestEnd cs (F + 1) σ (litVar ℓ) = some b := by
            rw [deepestEnd_active_var_eq cs F σ T ℓ hany hact hh]; exact hb
          have hτ' : fixVar σ (litVar ℓ) ((deepestEnd cs (F + 1) σ (litVar ℓ)).getD false) = σ' := by
            rw [hev, Option.getD_some, hσ', hstep]
            by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                          (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
            · rw [if_pos hd]; congr 1
              have := hb; rw [hstep, if_pos hd, fixVar, Function.update_self, Option.some_inj] at this
              exact this.symm
            · rw [if_neg hd]; congr 1
              have := hb; rw [hstep, if_neg hd, fixVar, Function.update_self, Option.some_inj] at this
              exact this.symm
          have hend : deepestEnd cs (F + 1) σ = deepestEnd cs F σ' := by rw [deepestEnd_succ, hσ']
          rw [hseq, hsel, hact]
          simp only [skipDecode, hcla, hτ']
          refine congrArg (insert (litVar ℓ)) ?_
          rw [hend]
          cases hany' : SwitchingCounting.anyTermSat cs σ' with
          | true =>
            rw [deepestSkipSeq_anyTermSat cs F σ' hany', deepestSel_anyTermSat cs F σ' hany',
              skipDecode]
          | false =>
            refine ih σ' _ ?_
            by_cases hadvv : adv = true
            · rw [if_pos hadvv]
            · rw [if_neg hadvv]
              -- bridge `σ'` (= `deepestStep`) to the `fixVar` form the per-step lemma expects
              obtain ⟨bb, hbb⟩ : ∃ bb, σ' = fixVar σ (litVar ℓ) bb := by
                by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
                · exact ⟨false, by rw [hσ', hstep, if_pos hd]⟩
                · exact ⟨true, by rw [hσ', hstep, if_neg hd]⟩
              have hbitfalse : (SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) bb) T ||
                  decide ((SwitchingCounting.freeLits (fixVar σ (litVar ℓ) bb) T).length = 0)) = false := by
                have hadvf : adv = false := by cases hadv2 : adv <;> simp_all
                rw [hadv, hbb] at hadvf; exact hadvf
              rw [hbb]
              exact (advanceBit_false_iff_active_persists hact hh (hbb ▸ hany')).mp hbitfalse

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.skipDecode_deepestSkipSeq

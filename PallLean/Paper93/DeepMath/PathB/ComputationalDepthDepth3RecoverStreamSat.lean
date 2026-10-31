import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverStreamCorrect

/-!
# `recoverStream` works for satisfied leaves too — `hleaf` is plumbing (branch only)

`recoverStream_eq` carries the hypothesis `anyTermSat cs (deepestEnd cs F σ) = false` (the leaf is
*unsatisfied*).  But the active-clause stream is only ever read at the **intermediate** descent states
`σ₀,…,σ_{s-1}`, and those are unsatisfied *inherently* — the canonical descent only takes a step from
an unsatisfied state (`if anyTermSat … then leaf`).  So `anyTermSat σ = false` is recoverable locally
from `activeTerm cs σ = some T` (`activeTerm_anyTermSat_false`), never from the leaf.

Hence `recoverStream_eq` holds **without** `hleaf`: the decoder recovers the active-clause stream even
when the deepest leaf is *satisfied* (a `true` leaf).  This removes the satisfied-leaf restriction at
the level of the core engine.

* `recoverStream_eq_sat` — `recoverStream_eq` with the `hleaf` hypothesis dropped.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.

**Honest scope.**  This is the *engine*-level removal of `hleaf`.  Propagating it through the count
chain (`recoverStream_correct` → `reconstructionCorrect_fullpath` → `fullpath_switching_count` →
`shell_count`) to drop `hleaf` from the count itself is separate plumbing; this file proves the load-
bearing step that it is possible.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The active literal's variable is free at the descent state. -/
private theorem head_free_sat {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) : σ (litVar ℓ) = none := by
  have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
  have hfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hmem).2
  rw [litFree_var] at hfree
  cases hx : σ (litVar ℓ) with
  | none => rfl
  | some _ => rw [hx] at hfree; simp at hfree

/-- **`recoverStream` correctness without the unsatisfied-leaf hypothesis.**  The running state `τ`
stays sub-restriction-and-falsification-synchronised with the descent state, computing the same active
clause at every step — and `anyTermSat σ = false` is derived locally from `activeTerm cs σ = some T`,
so the deepest leaf may be *satisfied*. -/
theorem recoverStream_eq_sat (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ τ : Fin n → Option Bool),
      SubRestriction τ σ →
      (∀ U ∈ cs, SwitchingCounting.termFalsified τ U = SwitchingCounting.termFalsified σ U) →
      recoverStream cs (deepestEnd cs F σ) ((deepestFullSeq cs F σ).map Prod.fst) τ
        = activeStreamPar cs F σ := by
  intro F
  induction F with
  | zero => intro σ τ _ _; rfl
  | succ F ih =>
    intro σ τ hsub hfal
    cases hact : SwitchingCounting.activeTerm cs σ with
    | none =>
      rw [show deepestFullSeq cs (F + 1) σ = [] by
            rw [deepestFullSeq]; cases hany : SwitchingCounting.anyTermSat cs σ <;> simp [hany, hact],
          show activeStreamPar cs (F + 1) σ = [] by
            rw [activeStreamPar]; cases hany : SwitchingCounting.anyTermSat cs σ <;> simp [hany, hact]]
      rfl
    | some T =>
      have hσ : SwitchingCounting.anyTermSat cs σ = false :=
        SwitchingCounting.activeTerm_anyTermSat_false hact
      have hτ : SwitchingCounting.anyTermSat cs τ = false := anyTermSat_false_of_sub hsub hσ
      cases hh : (SwitchingCounting.freeLits σ T).head? with
      | none =>
        rw [show deepestFullSeq cs (F + 1) σ = [] by rw [deepestFullSeq]; simp [hσ, hact, hh],
            show activeStreamPar cs (F + 1) σ = [] by rw [activeStreamPar]; simp [hσ, hact, hh]]
        rfl
      | some ℓ =>
        have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
          unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
        have heng : SwitchingCounting.activeTerm cs τ = some T := by
          rw [activeTerm_eq_of_falsified_agree hfal hτ hσ, hact]
        have hcla : clauseLitAt T (pivotPosOf cs σ) = some ℓ := by
          rw [clauseLitAt_pivotPosOf hact (by rw [hatl]; rfl)]; exact hatl
        have hσv : σ (litVar ℓ) = none := head_free_sat hh
        have hτv : τ (litVar ℓ) = none := sub_free hsub hσv
        have step : ∀ (bit : Bool),
            deepestStep cs F σ = fixVar σ (litVar ℓ) bit →
            (deepestFullSeq cs (F + 1) σ).map Prod.fst
              = pivotPosOf cs σ :: (deepestFullSeq cs F (fixVar σ (litVar ℓ) bit)).map Prod.fst →
            activeStreamPar cs (F + 1) σ
              = T :: activeStreamPar cs F (fixVar σ (litVar ℓ) bit) →
            recoverStream cs (deepestEnd cs (F + 1) σ) ((deepestFullSeq cs (F + 1) σ).map Prod.fst) τ
              = activeStreamPar cs (F + 1) σ := by
          intro bit hds hdf has
          have hsucc : deepestEnd cs (F + 1) σ = deepestEnd cs F (fixVar σ (litVar ℓ) bit) := by
            rw [deepestEnd_succ, hds]
          have hσend : deepestEnd cs (F + 1) σ (litVar ℓ) = some bit := by
            rw [deepestEnd_active_var_eq cs F σ T ℓ hσ hact hh, hds, fixVar, Function.update_self]
          rw [hdf, has, recoverStream]
          simp only [heng, hcla, hσend, Option.getD_some]
          congr 1
          rw [hsucc]
          exact ih (fixVar σ (litVar ℓ) bit) (fixVar τ (litVar ℓ) bit)
            (subRestriction_fixVar hsub) (maintain_falsified_agree hτv hσv hfal)
        by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
            (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
        · refine step false (by rw [deepestStep_active cs F σ T hσ hact hh, if_pos hd]) ?_ ?_
          · rw [deepestFullSeq]; simp only [hσ, Bool.false_eq_true, if_false, hact, hh, if_pos hd,
              List.map_cons]
          · rw [activeStreamPar]; simp only [hσ, Bool.false_eq_true, if_false, hact, hh, if_pos hd]
        · refine step true (by rw [deepestStep_active cs F σ T hσ hact hh, if_neg hd]) ?_ ?_
          · rw [deepestFullSeq]; simp only [hσ, Bool.false_eq_true, if_false, hact, hh, if_neg hd,
              List.map_cons]
          · rw [activeStreamPar]; simp only [hσ, Bool.false_eq_true, if_false, hact, hh, if_neg hd]

/-- **The decoder recovers the active stream of a bad ρ — even for a satisfied leaf.**  Starting from
the all-free state, `recoverStream` equals `activeStreamPar cs F ρ`, needing only `hnf` (ρ falsifies
nothing); the unsatisfied-leaf hypothesis is gone. -/
theorem recoverStream_correct_sat (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hnf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false) :
    recoverStream cs (deepestEnd cs F ρ) ((deepestFullSeq cs F ρ).map Prod.fst) (fun _ => none)
      = activeStreamPar cs F ρ := by
  refine recoverStream_eq_sat cs F ρ (fun _ => none) (fun j hj => absurd rfl hj) ?_
  intro U hU
  rw [show SwitchingCounting.termFalsified (fun _ => none) U = false by
        rw [SwitchingCounting.termFalsified, List.any_eq_false]
        intro m _
        have hm : SwitchingCounting.litFalse (fun _ : Fin n => none) m = false :=
          litFalse_free_eq_false (ρ := fun _ => none) (m := m) rfl
        simp [hm],
      hnf U hU]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recoverStream_eq_sat
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recoverStream_correct_sat

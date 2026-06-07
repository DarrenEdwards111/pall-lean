import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SubRestriction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullReplayCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatisfyStepRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPositionLit

/-!
# `recoverStream` and its correctness — the recursive reconstruction, completed (branch only)

The concrete leaf-only decoder for the active-clause stream, and the proof it reproduces
`activeStreamPar`.  This closes the recursive reconstruction: the running state `τ` (queried variables
read off the leaf) stays sub-restriction-and-falsification-synchronised with the descent state, so it
computes the same active clause at every step.

* `recoverStream cs σ_end positions τ` — walk the recorded `positions`; at each, take `activeTerm cs τ`,
  read the literal at that position, set its variable to the leaf value, cons the clause, recurse.
  Legal data only: `σ_end`, `cs`, the positions.
* `recoverStream_eq` — **the correctness**: for `τ ⊑ σ`, falsification-agreeing, with an unsatisfied
  leaf, `recoverStream cs (deepestEnd cs F σ) ((deepestFullSeq cs F σ).map .1) τ = activeStreamPar cs F σ`.
* `recoverStream_correct` — instantiated at the genuine bad `ρ` from the all-free start: the decoder
  recovers the active-clause stream of `ρ` from the leaf and the recorded positions, with no `ρ`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The leaf-only active-stream decoder.**  At each recorded position, the active clause of the
running state, the literal at that position, fixed to its leaf value; cons and recurse. -/
def recoverStream (cs : List (Clause n)) (σ_end : Fin n → Option Bool) :
    List ℕ → (Fin n → Option Bool) → List (Clause n)
  | [], _ => []
  | p :: ps, τ =>
      match SwitchingCounting.activeTerm cs τ with
      | none => []
      | some T =>
          match clauseLitAt T p with
          | none => []
          | some m =>
              T :: recoverStream cs σ_end ps (fixVar τ (litVar m) ((σ_end (litVar m)).getD false))

/-- The active literal's variable is free at the descent state. -/
private theorem head_litVar_free {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) : σ (litVar ℓ) = none := by
  have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
  have hfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hmem).2
  rw [litFree_var] at hfree
  cases hx : σ (litVar ℓ) with
  | none => rfl
  | some _ => rw [hx] at hfree; simp at hfree

/-- **Correctness of `recoverStream`.**  Carrying the invariant `SubRestriction τ σ ∧ falsification-
agreement`, the decoder reproduces the descent's active-clause stream. -/
theorem recoverStream_eq (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ τ : Fin n → Option Bool),
      SubRestriction τ σ →
      (∀ U ∈ cs, SwitchingCounting.termFalsified τ U = SwitchingCounting.termFalsified σ U) →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false →
      recoverStream cs (deepestEnd cs F σ) ((deepestFullSeq cs F σ).map Prod.fst) τ
        = activeStreamPar cs F σ := by
  intro F
  induction F with
  | zero => intro σ τ _ _ _; rfl
  | succ F ih =>
    intro σ τ hsub hfal hleaf
    have hσ : SwitchingCounting.anyTermSat cs σ = false :=
      anyTermSat_of_deepestEnd_false cs (F + 1) σ hleaf
    have hτ : SwitchingCounting.anyTermSat cs τ = false := anyTermSat_false_of_sub hsub hσ
    cases hact : SwitchingCounting.activeTerm cs σ with
    | none =>
      rw [show deepestFullSeq cs (F + 1) σ = [] by rw [deepestFullSeq]; simp [hσ, hact],
          show activeStreamPar cs (F + 1) σ = [] by rw [activeStreamPar]; simp [hσ, hact]]
      rfl
    | some T =>
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
        have hσv : σ (litVar ℓ) = none := head_litVar_free hh
        have hτv : τ (litVar ℓ) = none := sub_free hsub hσv
        -- a generic deepest branch with chosen bit
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
          refine ih (fixVar σ (litVar ℓ) bit) (fixVar τ (litVar ℓ) bit)
            (subRestriction_fixVar hsub)
            (maintain_falsified_agree hτv hσv hfal) ?_
          rw [← hsucc]; exact hleaf
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

/-- **The decoder recovers the active stream of a bad ρ from the leaf alone.**  Starting from the
all-free state, `recoverStream` (legal data: leaf + recorded positions + `cs`) equals
`activeStreamPar cs F ρ`. -/
theorem recoverStream_correct (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hnf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    recoverStream cs (deepestEnd cs F ρ) ((deepestFullSeq cs F ρ).map Prod.fst) (fun _ => none)
      = activeStreamPar cs F ρ := by
  refine recoverStream_eq cs F ρ (fun _ => none) (fun j hj => absurd rfl hj) ?_ hleaf
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

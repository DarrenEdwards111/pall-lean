import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MaintainInvariant

/-!
# Sub-restriction infrastructure for the recursive reconstruction — branch only

The recursion carries the invariant `SubRestriction τ σ ∧ falsification-agreement`.  `SubRestriction`
(`τ` assigns a subset of what `σ` assigns, agreeing) supplies the two facts the engine needs beyond
falsification-agreement:

* `anyTermSat_false_of_sub` — `τ ⊑ σ` and `σ` satisfies nothing ⟹ `τ` satisfies nothing (so the engine
  `activeTerm_eq_of_falsified_agree` applies to `τ` too).  Via `litTrue_mono`.
* `sub_free` — if `σ` leaves `v` free then so does `τ` (so the maintain-invariant step applies).
* `subRestriction_fixVar` — fixing the same variable to the same value on both sides preserves `⊑`.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `τ` is a sub-restriction of `σ`: it assigns a subset of `σ`'s assignments, agreeing where set. -/
def SubRestriction (τ σ : Fin n → Option Bool) : Prop :=
  ∀ j, τ j ≠ none → σ j = τ j

/-- If `τ ⊑ σ` and `σ` satisfies no clause, then `τ` satisfies no clause. -/
theorem anyTermSat_false_of_sub {cs : List (Clause n)} {τ σ : Fin n → Option Bool}
    (hsub : SubRestriction τ σ) (hσ : SwitchingCounting.anyTermSat cs σ = false) :
    SwitchingCounting.anyTermSat cs τ = false := by
  by_contra hc
  rw [Bool.not_eq_false, SwitchingCounting.anyTermSat, List.any_eq_true] at hc
  obtain ⟨U, hU, hsat⟩ := hc
  have hsatσ : SwitchingCounting.termSat σ U = true := by
    rw [SwitchingCounting.termSat, List.all_eq_true] at hsat ⊢
    intro m hm
    exact litTrue_mono hsub (hsat m hm)
  have : SwitchingCounting.anyTermSat cs σ = true := by
    rw [SwitchingCounting.anyTermSat, List.any_eq_true]; exact ⟨U, hU, hsatσ⟩
  rw [hσ] at this; exact absurd this (by simp)

/-- If `σ` leaves `v` free, so does `τ`. -/
theorem sub_free {τ σ : Fin n → Option Bool} {v : Fin n}
    (hsub : SubRestriction τ σ) (hv : σ v = none) : τ v = none := by
  by_contra h
  rw [hsub v h] at hv
  exact h hv

/-- Fixing the same variable to the same value on both sides preserves `SubRestriction`. -/
theorem subRestriction_fixVar {τ σ : Fin n → Option Bool} {v : Fin n} {b : Bool}
    (hsub : SubRestriction τ σ) : SubRestriction (fixVar τ v b) (fixVar σ v b) := by
  intro j hj
  by_cases hjv : j = v
  · subst hjv
    rw [fixVar, fixVar, Function.update_self, Function.update_self]
  · rw [fixVar, Function.update_of_ne hjv] at hj ⊢
    rw [fixVar, Function.update_of_ne hjv]
    exact hsub j hj

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.anyTermSat_false_of_sub
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.subRestriction_fixVar

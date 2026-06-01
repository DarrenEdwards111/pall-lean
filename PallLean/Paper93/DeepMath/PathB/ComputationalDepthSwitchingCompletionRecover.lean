import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingRevPeel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletion

/-!
# The completion is invertible: `revPeel σ* (path vars) = ρ`

**STATUS: REAL.  THE σ* RECOVERY SKELETON (value-agnostic).**

The recovery half of `decode_encode_id` for the satisfying-completion layer: peeling
the path's variables off the completion `σ* = complete ρ litList` returns `ρ`.  This is
*value-agnostic* — it uses only that `σ*` agrees with `ρ` off the path variables and that
`ρ` leaves them free, so it works for the satisfying completion exactly as for the
falsify path.  The satisfying values matter for the *decoder* (identifying processed
clauses), not for this skeleton.

* `revPeel_apply`: `revPeel σ vs j = if j ∈ vs then none else σ j`;
* `complete_apply_eq_of_not_mem`: the completion is unchanged off the path variables;
* `revPeel_complete`: `revPeel (complete ρ litList) (litList.map litVar) = ρ` when `ρ`
  is free on the path variables.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The reverse peel sets exactly the listed variables to free. -/
theorem revPeel_apply (σ : Restriction n) (vs : List (Fin n)) (j : Fin n) :
    revPeel σ vs j = if j ∈ vs then none else σ j := by
  induction vs generalizing σ with
  | nil => simp [revPeel]
  | cons v vs ih =>
    rw [revPeel_cons, ih]
    by_cases hjvs : j ∈ vs <;> by_cases hjv : j = v <;>
      simp [hjvs, hjv, List.mem_cons, freeOn, Finset.mem_singleton]

/-- The completion is unchanged on variables outside the path's literal list. -/
theorem complete_apply_eq_of_not_mem (ρ : Restriction n) (litList : List (Rung4Literal n))
    (j : Fin n) (h : j ∉ litList.map litVar) : complete ρ litList j = ρ j := by
  induction litList generalizing ρ with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [complete_cons, ih (satFix ρ a) h.2]
    exact satFix_eq_outside ρ a h.1

/-- **The completion is invertible.**  Peeling the path's variables off the satisfying
completion returns `ρ` (given `ρ` is free on those variables). -/
theorem revPeel_complete {ρ : Restriction n} {litList : List (Rung4Literal n)}
    (hfree : ∀ ℓ ∈ litList, ρ (litVar ℓ) = none) :
    revPeel (complete ρ litList) (litList.map litVar) = ρ := by
  funext j
  rw [revPeel_apply]
  by_cases hj : j ∈ litList.map litVar
  · rw [if_pos hj]
    obtain ⟨ℓ, hℓ, hjv⟩ := List.mem_map.mp hj
    rw [← hjv]; exact (hfree ℓ hℓ).symm
  · rw [if_neg hj]
    exact complete_apply_eq_of_not_mem ρ litList j hj

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.revPeel_complete

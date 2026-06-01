import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletion

/-!
# Processed clauses are exactly the satisfaction-flips

**STATUS: REAL.  THE DISTINGUISHING CORE OF THE FORWARD DECODER.**

The remaining design question for the σ* decoder was: how to tell a *processed* clause
(satisfied under σ* by a chosen literal) from a clause merely *satisfied by ρ* — both
look satisfied under σ*.  The answer is the **satisfaction flip**, and it is exact:

* `clause_processed_of_flip`: if a clause is satisfied under the completion but
  *unsatisfied under ρ*, then it contains a path variable (it was processed) — because
  the only difference between σ* and ρ is the path variables, so a flip can only be
  caused by one of them;
* `clause_unflipped_of_disjoint`: conversely a clause with no path variable has the same
  status under σ* and ρ (no flip).

This is the "free-and-confirm" test made precise: freeing a clause's labelled variables
takes σ* back to ρ on that clause; a flip from satisfied to unsatisfied confirms the
clause was processed, distinguishing it from a ρ-satisfied clause (which never flips).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **The distinguishing core.**  A clause satisfied under the completion but unsatisfied
under `ρ` must contain a path variable — the flip can only be caused by a path variable,
since `σ*` and `ρ` differ only there. -/
theorem clause_processed_of_flip {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {C : Clause n}
    (hsat : clauseSatisfied (complete ρ litList) C = true)
    (hunsat : clauseSatisfied ρ C = false) :
    ∃ ℓ' ∈ C.lits, litVar ℓ' ∈ litList.map litVar := by
  rw [clauseSatisfied, List.any_eq_true] at hsat
  obtain ⟨ℓ', hℓ'C, hℓ'true⟩ := hsat
  refine ⟨ℓ', hℓ'C, ?_⟩
  by_contra hnotmem
  rw [litTrue_complete_eq_of_not_mem ℓ' litList ρ hnotmem] at hℓ'true
  have : clauseSatisfied ρ C = true := by
    rw [clauseSatisfied, List.any_eq_true]; exact ⟨ℓ', hℓ'C, hℓ'true⟩
  rw [this] at hunsat
  exact absurd hunsat (by simp)

/-- Conversely, a clause with no path variable does not flip: its satisfaction status is
the same under `σ*` and `ρ`. -/
theorem clause_unflipped_of_disjoint {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {C : Clause n} (hdis : ∀ ℓ ∈ C.lits, litVar ℓ ∉ litList.map litVar) :
    clauseSatisfied (complete ρ litList) C = clauseSatisfied ρ C :=
  clauseSatisfied_complete_eq_of_disjoint hdis

/-- **Contrapositive form (decoder-facing).**  If a clause has *no* path variable, then it
is satisfied under `σ*` exactly when it is satisfied under `ρ` — so an unsatisfied-under-ρ
clause stays unsatisfied under `σ*`, and the decoder never mistakes it for processed. -/
theorem not_processed_of_no_path_var {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {C : Clause n} (hdis : ∀ ℓ ∈ C.lits, litVar ℓ ∉ litList.map litVar)
    (hunsat : clauseSatisfied ρ C = false) :
    clauseSatisfied (complete ρ litList) C = false := by
  rw [clause_unflipped_of_disjoint hdis, hunsat]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clause_processed_of_flip
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.not_processed_of_no_path_var

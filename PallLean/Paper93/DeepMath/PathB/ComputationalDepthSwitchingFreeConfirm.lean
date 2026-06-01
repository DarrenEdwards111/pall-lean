import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletionRecover

/-!
# The free-and-confirm primitive: `freeOn σ*` reproduces `ρ`-satisfaction

**STATUS: REAL.  THE DECODER'S OPERATIONAL FLIP TEST = ρ-SATISFACTION.**

The forward decoder operates on `σ*` via `freeOn`, not on the abstract `ρ`.  This file
proves the bridge: freeing a clause's path variables from `σ*` reproduces exactly `ρ`'s
satisfaction status on that clause.  So the decoder's *executable* test — "is `C`
satisfied under `σ*` but unsatisfied after freeing its path variables?" — equals the
abstract flip test (`clause_processed_of_flip`), and confirms `C` was processed.

* `litTrue_eq_of_agree`: forced truth depends only on the literal's own variable;
* `clauseSatisfied_freeOn_complete_eq`: if the freed set `S` matches the path variables
  on `C`'s variables (and `ρ` is free on path variables), then
  `clauseSatisfied (freeOn (complete ρ litList) S) C = clauseSatisfied ρ C`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Forced truth depends only on the literal's own variable. -/
theorem litTrue_eq_of_agree {σ τ : Restriction n} {ℓ : Rung4Literal n}
    (h : σ (litVar ℓ) = τ (litVar ℓ)) : Depth3.litTrue σ ℓ = Depth3.litTrue τ ℓ := by
  cases ℓ <;> (simp only [litVar] at h; simp only [Depth3.litTrue, Depth3.litFixedVal, h])

/-- On `C`'s variables, freeing the path-matching set takes `σ*` back to `ρ`. -/
theorem freeOn_complete_agree {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {S : Finset (Fin n)} {ℓ : Rung4Literal n}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hiff : litVar ℓ ∈ S ↔ litVar ℓ ∈ litList.map litVar) :
    (freeOn (complete ρ litList) S) (litVar ℓ) = ρ (litVar ℓ) := by
  simp only [freeOn]
  by_cases hmem : litVar ℓ ∈ S
  · rw [if_pos hmem]
    exact (hfree (litVar ℓ) (hiff.mp hmem)).symm
  · rw [if_neg hmem]
    exact complete_apply_eq_of_not_mem ρ litList (litVar ℓ) (fun h => hmem (hiff.mpr h))

/-- Per-element agreement of `litTrue` lifts to `any` over a literal list. -/
theorem any_litTrue_freeOn_complete_eq {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {S : Finset (Fin n)} (hfree : ∀ v ∈ litList.map litVar, ρ v = none) :
    ∀ (lst : List (Rung4Literal n)),
      (∀ ℓ ∈ lst, (litVar ℓ ∈ S ↔ litVar ℓ ∈ litList.map litVar)) →
      lst.any (Depth3.litTrue (freeOn (complete ρ litList) S)) = lst.any (Depth3.litTrue ρ) := by
  intro lst
  induction lst with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.any_cons, List.any_cons,
      litTrue_eq_of_agree (freeOn_complete_agree hfree (h a (List.mem_cons.mpr (Or.inl rfl)))),
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

/-- **Free-and-confirm primitive.**  If the freed set `S` matches the path variables on
`C`'s variables, then freeing it from `σ*` reproduces `ρ`'s satisfaction status on `C` —
so the decoder's executable flip test equals the abstract `ρ`-test. -/
theorem clauseSatisfied_freeOn_complete_eq {ρ : Restriction n}
    {litList : List (Rung4Literal n)} {S : Finset (Fin n)} {C : Clause n}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hS : ∀ ℓ ∈ C.lits, (litVar ℓ ∈ S ↔ litVar ℓ ∈ litList.map litVar)) :
    clauseSatisfied (freeOn (complete ρ litList) S) C = clauseSatisfied ρ C := by
  unfold clauseSatisfied
  exact any_litTrue_freeOn_complete_eq hfree C.lits hS

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseSatisfied_freeOn_complete_eq

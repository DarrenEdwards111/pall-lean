import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActive

/-!
# The satisfying completion: processed clauses become identifiable

**STATUS: REAL.  FIRST THEOREM OF THE FAITHFUL HÅSTAD σ* LAYER.**

The falsify path supports clean reverse peeling, but boundary clause-identity depends
on hidden path history, and dead clauses (clauses ρ already falsified) make reverse
clause recovery ambiguous.  The faithful Håstad device fixes this by recording the
*satisfying completion* `σ* = complete ρ (path literals)` — set each chosen literal's
variable to its **satisfying** value rather than its falsifying one.

This file proves the design works at the level that matters:

* `clauseSatisfied_complete_of_mem`: a **processed** clause (one whose literal was
  chosen along the path) is *satisfied* under the completion — so processed clauses are
  identifiable from `σ*` alone, not from path history;
* `clauseSatisfied_complete_eq_of_disjoint`: a clause sharing no variable with the path
  is *unchanged* under the completion — so a **dead** clause (unsatisfied under ρ, never
  processed) stays unsatisfied, and no longer creates boundary ambiguity.

If this holds, the multi-clause decoder has a route; these are the load-bearing facts.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- `satFix` forces its own literal true. -/
theorem litTrue_satFix_self (ρ : Restriction n) (ℓ : Rung4Literal n) :
    Depth3.litTrue (satFix ρ ℓ) ℓ = true := by
  simp [Depth3.litTrue, satFix_forces]

/-- `satFix` leaves the forced value of literals on *other* variables unchanged. -/
theorem litFixedVal_satFix_ne (ρ : Restriction n) (ℓ : Rung4Literal n) {ℓ' : Rung4Literal n}
    (h : litVar ℓ' ≠ litVar ℓ) :
    Depth3.litFixedVal (satFix ρ ℓ) ℓ' = Depth3.litFixedVal ρ ℓ' := by
  cases ℓ' with
  | pos i =>
    simp only [Depth3.litFixedVal]
    exact satFix_eq_outside ρ ℓ (by simpa [litVar] using h)
  | neg i =>
    simp only [Depth3.litFixedVal]
    rw [satFix_eq_outside ρ ℓ (by simpa [litVar] using h)]

theorem litTrue_satFix_ne (ρ : Restriction n) (ℓ : Rung4Literal n) {ℓ' : Rung4Literal n}
    (h : litVar ℓ' ≠ litVar ℓ) :
    Depth3.litTrue (satFix ρ ℓ) ℓ' = Depth3.litTrue ρ ℓ' := by
  unfold Depth3.litTrue; rw [litFixedVal_satFix_ne ρ ℓ h]

/-- The **satisfying completion**: set each literal of `litList` to its satisfying value. -/
def complete (ρ : Restriction n) (litList : List (Rung4Literal n)) : Restriction n :=
  litList.foldl satFix ρ

theorem complete_cons (ρ : Restriction n) (a : Rung4Literal n) (l : List (Rung4Literal n)) :
    complete ρ (a :: l) = complete (satFix ρ a) l := by
  simp only [complete, List.foldl_cons]

/-- On a variable not touched by the completion, the forced truth is unchanged. -/
theorem litTrue_complete_eq_of_not_mem (ℓ : Rung4Literal n) :
    ∀ (litList : List (Rung4Literal n)) (ρ : Restriction n),
      litVar ℓ ∉ litList.map litVar →
      Depth3.litTrue (complete ρ litList) ℓ = Depth3.litTrue ρ ℓ := by
  intro litList
  induction litList with
  | nil => intro ρ _; rfl
  | cons a l ih =>
    intro ρ h
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [complete_cons, ih (satFix ρ a) h.2, litTrue_satFix_ne ρ a h.1]

/-- A literal of the completion's list (distinct variables) is forced true. -/
theorem litTrue_complete_of_mem :
    ∀ (litList : List (Rung4Literal n)) (ρ : Restriction n) (ℓ : Rung4Literal n),
      ℓ ∈ litList → (litList.map litVar).Nodup →
      Depth3.litTrue (complete ρ litList) ℓ = true := by
  intro litList
  induction litList with
  | nil => intro ρ ℓ h _; simp at h
  | cons a l ih =>
    intro ρ ℓ hℓ hnd
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [complete_cons]
    rcases List.mem_cons.mp hℓ with rfl | hℓ'
    · rw [litTrue_complete_eq_of_not_mem ℓ l (satFix ρ ℓ) hnd.1]
      exact litTrue_satFix_self ρ ℓ
    · exact ih (satFix ρ a) ℓ hℓ' hnd.2

/-- **Processed clauses are satisfied under the completion.**  If a literal chosen along
the path (`ℓ ∈ litList`, distinct variables) belongs to clause `C`, then `C` is satisfied
under the completion — identifiable from `σ*` with no path history. -/
theorem clauseSatisfied_complete_of_mem {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {C : Clause n} {ℓ : Rung4Literal n}
    (hℓlit : ℓ ∈ litList) (hℓC : ℓ ∈ C.lits) (hnd : (litList.map litVar).Nodup) :
    clauseSatisfied (complete ρ litList) C = true := by
  rw [clauseSatisfied, List.any_eq_true]
  exact ⟨ℓ, hℓC, litTrue_complete_of_mem litList ρ ℓ hℓlit hnd⟩

/-- `any litTrue` agrees with the completion on a list of literals disjoint from the
path's variables. -/
theorem any_litTrue_complete_eq (ρ : Restriction n) (litList : List (Rung4Literal n)) :
    ∀ (lst : List (Rung4Literal n)), (∀ x ∈ lst, litVar x ∉ litList.map litVar) →
      lst.any (Depth3.litTrue (complete ρ litList)) = lst.any (Depth3.litTrue ρ) := by
  intro lst
  induction lst with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.any_cons, List.any_cons,
      litTrue_complete_eq_of_not_mem a litList ρ (h a (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

/-- **Dead clauses are unchanged by the completion.**  A clause sharing no variable with
the path keeps its satisfaction status — so a dead clause (unsatisfied under ρ) stays
unsatisfied, removing boundary ambiguity. -/
theorem clauseSatisfied_complete_eq_of_disjoint {ρ : Restriction n}
    {litList : List (Rung4Literal n)} {C : Clause n}
    (hdis : ∀ ℓ ∈ C.lits, litVar ℓ ∉ litList.map litVar) :
    clauseSatisfied (complete ρ litList) C = clauseSatisfied ρ C := by
  unfold clauseSatisfied
  exact any_litTrue_complete_eq ρ litList C.lits hdis

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseSatisfied_complete_of_mem
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseSatisfied_complete_eq_of_disjoint

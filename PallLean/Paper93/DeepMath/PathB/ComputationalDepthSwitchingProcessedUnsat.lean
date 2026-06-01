import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStable2

/-!
# Processed clauses are unsatisfied under ρ

**STATUS: REAL.  SUPPORT FOR THE FORWARD-DECODER FLIP.**

For the free-and-confirm test to *flip* on a processed clause, the clause must be
unsatisfied under `ρ`.  A processed clause is the active clause at some step, hence
unsatisfied under the more-fixed `actPath cs ρ i`; this propagates down to `ρ` by
monotonicity: the path only fixes `ρ`-free variables, so it agrees with `ρ` wherever
`ρ` is fixed, and a forced-true literal stays forced true under more fixing.

* `litTrue_mono` / `clauseSatisfied_mono`: satisfaction is monotone under extension;
* `actPath_extends`: the path agrees with `ρ` on `ρ`-fixed variables;
* `clauseSatisfied_ρ_false_of_active`: the active clause at any step is unsatisfied
  under `ρ`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Forced truth is monotone under extension (fixing more variables keeps truths). -/
theorem litTrue_mono {ρ σ : Restriction n} {ℓ : Rung4Literal n}
    (hext : ∀ j, ρ j ≠ none → σ j = ρ j) (h : Depth3.litTrue ρ ℓ = true) :
    Depth3.litTrue σ ℓ = true := by
  have hfix : Depth3.litFixedVal ρ ℓ = some true := litFixedVal_some_of_litTrue h
  have hne : ρ (litVar ℓ) ≠ none := by
    cases ℓ with
    | pos i => simp only [Depth3.litFixedVal] at hfix; simp only [litVar]; rw [hfix]; simp
    | neg i =>
      simp only [Depth3.litFixedVal] at hfix
      simp only [litVar]; intro hc; rw [hc] at hfix; simp at hfix
  have hvar : σ (litVar ℓ) = ρ (litVar ℓ) := hext _ hne
  have hfixσ : Depth3.litFixedVal σ ℓ = some true := by
    cases ℓ with
    | pos i =>
      simp only [Depth3.litFixedVal] at hfix ⊢; simp only [litVar] at hvar; rw [hvar]; exact hfix
    | neg i =>
      simp only [Depth3.litFixedVal] at hfix ⊢; simp only [litVar] at hvar; rw [hvar]; exact hfix
  simp only [Depth3.litTrue, hfixσ]

/-- Clause satisfaction is monotone under extension. -/
theorem clauseSatisfied_mono {ρ σ : Restriction n} {C : Clause n}
    (hext : ∀ j, ρ j ≠ none → σ j = ρ j) (h : clauseSatisfied ρ C = true) :
    clauseSatisfied σ C = true := by
  rw [clauseSatisfied, List.any_eq_true] at h ⊢
  obtain ⟨ℓ, hℓ, ht⟩ := h
  exact ⟨ℓ, hℓ, litTrue_mono hext ht⟩

/-- The path agrees with `ρ` on `ρ`-fixed variables (it only fixes free ones). -/
theorem actPath_extends (cs : List (Clause n)) (ρ : Restriction n) (i : ℕ) {j : Fin n}
    (h : ρ j ≠ none) : actPath cs ρ i j = ρ j :=
  actPath_eq_outside cs ρ i (fun hj => h (mem_freeVars.mp (actSel_subset_freeVars cs ρ i hj)))

/-- A clause unsatisfied under the path's state is unsatisfied under `ρ`. -/
theorem clauseSatisfied_ρ_false_of_actPath {cs : List (Clause n)} {ρ : Restriction n}
    {i : ℕ} {C : Clause n} (h : clauseSatisfied (actPath cs ρ i) C = false) :
    clauseSatisfied ρ C = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [clauseSatisfied_mono (fun j hj => actPath_extends cs ρ i hj) hc] at h
  simp at h

/-- **The active clause at any step is unsatisfied under `ρ`.**  So the free-and-confirm
test genuinely flips on a processed clause. -/
theorem clauseSatisfied_ρ_false_of_active {cs : List (Clause n)} {ρ : Restriction n}
    {i : ℕ} {C : Clause n} (hC : activeClause cs (actPath cs ρ i) = some C) :
    clauseSatisfied ρ C = false :=
  clauseSatisfied_ρ_false_of_actPath (activeClause_unsat hC)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseSatisfied_ρ_false_of_active

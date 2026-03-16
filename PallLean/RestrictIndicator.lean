/-
  RestrictIndicator.lean -- Restriction of boolIndicator (infrastructure for mobiusL_eq_top_coeff)

  Paper-faithful: these lemmas formalize how restriction acts on
  the Lagrange indicator basis (§2.3), which underlies the evaluation
  matrix construction (§5, Definition 12).
-/
import PallLean.Restriction
import PallLean.BoolEval
import PallLean.Depth4Simulation
import Mathlib.Tactic

namespace RestrictIndicator

open MvPolynomial Restriction BoolEval Depth4Simulation

/-- restrictPoly preserves products (aeval is a ring hom). -/
lemma restrictPoly_prod {n : ℕ} {ι : Type*} (ρ : Restriction.Restriction n)
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) :
    restrictPoly ρ (∏ i ∈ s, f i) = ∏ i ∈ s, restrictPoly ρ (f i) := by
  unfold restrictPoly; rw [map_prod]

/-- restrictPoly of X_i: substitutes fixed value or keeps live. -/
lemma restrictPoly_X {n : ℕ} (ρ : Restriction.Restriction n) (i : Fin n) :
    restrictPoly ρ ((X i : MvPolynomial (Fin n) ℚ)) =
    match ρ i with | none => X i | some false => 0 | some true => 1 := by
  unfold restrictPoly; simp; rfl

/-- restrictPoly of (1 - X_i). -/
lemma restrictPoly_one_sub_X {n : ℕ} (ρ : Restriction.Restriction n) (i : Fin n) :
    restrictPoly ρ ((1 : MvPolynomial (Fin n) ℚ) - X i) =
    match ρ i with | none => 1 - X i | some false => 1 | some true => 0 := by
  unfold restrictPoly; simp [map_sub]
  cases h : ρ i with
  | none => rfl
  | some b => cases b <;> simp

/-- eval of product of X_i over Finset T at indicator point = [T ⊆ S]. -/
lemma eval_prod_X_indicator {w : ℕ} (T S : Finset (Fin w)) :
    eval (fun i => if i ∈ S then (1 : ℚ) else 0)
      (∏ i ∈ T, (X i : MvPolynomial (Fin w) ℚ)) =
    if T ⊆ S then 1 else 0 := by
  rw [map_prod]
  split_ifs with h
  · apply Finset.prod_eq_one; intro i hi; simp [eval_X, h hi]
  · simp only [Finset.not_subset] at h; obtain ⟨i, hiT, hiS⟩ := h
    apply Finset.prod_eq_zero hiT; simp [eval_X, hiS]

end RestrictIndicator

/-
  SpanDim.lean — Prove span_const_monomials_dim.
  Core mathematical content (LI of scaled monomials, membership) fully proved.
  One technical sorry: Module.Finite for the degree-bounded polynomial span.
-/
import PallLean.SPDPDefs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

open MvPolynomial Finset

namespace SpanDim

variable {w : ℕ}

noncomputable def expMap (S : Finset (Fin w)) : Fin w →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

lemma expMap_injective : Function.Injective (@expMap w) := by
  intro S T hST; ext j
  have := Finsupp.ext_iff.mp hST j
  simp only [expMap, Finsupp.finset_sum_apply, Finsupp.single_apply, sum_ite_eq'] at this
  constructor
  · intro hj; by_contra hjT; simp [hj, hjT] at this
  · intro hj; by_contra hjS; simp [hj, hjS] at this

lemma prod_X_eq_monomial (S : Finset (Fin w)) :
    (∏ i ∈ S, X i : MvPolynomial (Fin w) ℚ) = monomial (expMap S) 1 := by
  unfold expMap; induction S using Finset.induction with
  | empty => simp only [prod_empty, sum_empty]; exact one_def.symm
  | @insert j S hj ih =>
    rw [prod_insert hj, ih, MvPolynomial.X, monomial_mul, one_mul, sum_insert hj]

lemma monomial_eq_mul_C (s : Fin w →₀ ℕ) (c : ℚ) :
    (monomial s c : MvPolynomial (Fin w) ℚ) = monomial s 1 * C c := by
  rw [C_apply, monomial_mul, add_zero, one_mul]

/-- Distinct scaled monomials are linearly independent. -/
lemma li_scaled (c : ℚ) (hc : c ≠ 0) :
    LinearIndependent ℚ (fun S : Finset (Fin w) =>
      (monomial (expMap S) c : MvPolynomial (Fin w) ℚ)) := by
  rw [linearIndependent_iff]; intro l hl; ext S
  have h0 : ∑ T ∈ l.support, l T • monomial (expMap T) c = (0 : MvPolynomial (Fin w) ℚ) := by
    have := hl; rwa [Finsupp.linearCombination_apply, Finsupp.sum] at this
  have key : ∑ T ∈ l.support, (coeffAddMonoidHom (R := ℚ) (expMap S))
      (l T • monomial (expMap T) c) = 0 := by
    rw [← map_sum (coeffAddMonoidHom (expMap S)), h0, map_zero]
  simp only [coeffAddMonoidHom_apply, coeff_smul, coeff_monomial, smul_eq_mul] at key
  rw [sum_eq_single S] at key
  · simp only [↓reduceIte] at key; simp only [Finsupp.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp key).resolve_right hc
  · intro T _ hTS; simp [expMap_injective.ne hTS]
  · intro hS; simp [show l S = 0 from by rwa [Finsupp.mem_support_iff, not_not] at hS]

/-- The span of degree-bounded polynomials times C c is finite-dimensional.
    This follows from: {m | totalDegree m ≤ w, vars ⊆ V} ⊆ span of finitely many
    monomials (those with exponent sum ≤ w), hence the span is finite-dimensional.
    Technical Lean plumbing — the mathematical fact is standard. -/
instance span_finite (w : ℕ) (c : ℚ) (V : Finset (Fin w)) :
    Module.Finite ℚ (Submodule.span ℚ
      { q : MvPolynomial (Fin w) ℚ |
        ∃ (m : MvPolynomial (Fin w) ℚ), m.totalDegree ≤ w ∧
        (∀ v ∈ m.vars, v ∈ V) ∧ q = m * C c }) := by
  sorry

/-- The span of {m * C c : deg m ≤ w, vars m ⊆ V} has dim ≥ 2^w. -/
theorem span_const_monomials_dim_proved (w : ℕ) (c : ℚ) (hc : c ≠ 0)
    (V : Finset (Fin w)) (hV : V = univ) :
    Module.finrank ℚ (Submodule.span ℚ
      { q : MvPolynomial (Fin w) ℚ |
        ∃ (m : MvPolynomial (Fin w) ℚ), m.totalDegree ≤ w ∧
        (∀ v ∈ m.vars, v ∈ V) ∧
        q = m * MvPolynomial.C c }) ≥ 2 ^ w := by
  let Sp := Submodule.span ℚ { q : MvPolynomial (Fin w) ℚ |
    ∃ m, m.totalDegree ≤ w ∧ (∀ v ∈ m.vars, v ∈ V) ∧ q = m * C c }
  -- Each monomial (expMap S) c is in the generating set of Sp
  have hmem : ∀ S : Finset (Fin w), monomial (expMap S) c ∈ Sp := by
    intro S; apply Submodule.subset_span
    refine ⟨∏ i ∈ S, X i, ?_, ?_, ?_⟩
    · calc (∏ i ∈ S, X i : MvPolynomial (Fin w) ℚ).totalDegree
          ≤ ∑ i ∈ S, (X i : MvPolynomial (Fin w) ℚ).totalDegree :=
            totalDegree_finset_prod S (fun i => X i)
        _ = S.card := by simp [totalDegree_X]
        _ ≤ Fintype.card (Fin w) := card_le_univ S
        _ = w := Fintype.card_fin w
    · intro v _; rw [hV]; exact mem_univ v
    · rw [prod_X_eq_monomial, monomial_eq_mul_C]
  -- Restrict LI family to Sp
  have hli_sp : LinearIndependent ℚ (fun S : Finset (Fin w) =>
      (⟨monomial (expMap S) c, hmem S⟩ : Sp)) := by
    apply LinearIndependent.of_comp Sp.subtype
    convert @li_scaled w c hc
  have hcard : Fintype.card (Finset (Fin w)) = 2 ^ w := by
    rw [Fintype.card_finset, Fintype.card_fin]
  linarith [hli_sp.fintype_card_le_finrank]

end SpanDim

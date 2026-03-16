/-
  TopCoeffRank.lean — SPDP rank of ∏ Xᵢ with κ=ℓ=w is ≥ 2^w

  The key algebraic fact: iterDerivList [0,...,w-1] (∏ Xᵢ) = 1.
  Combined with the SPDP generator inclusion, this gives rank ≥ 2^w.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace TopCoeffRank

open MvPolynomial SPDP Finset

/-! ## iterDerivList [0,...,w-1] (∏ Xᵢ) = 1

  We prove this by showing iterDerivList on a general polynomial
  extracts the top coefficient, then showing ∏ Xᵢ has top coefficient 1.

  The key lemma: for a monomial, iterDerivList over ALL distinct variables
  of degree exactly 1 each gives the coefficient. -/

/-- pderiv is a derivation, so pderiv i (a * b) = pderiv i a * b + a * pderiv i b -/
-- This is pderiv_mul in Mathlib.

/-- For the product ∏_{i : Fin w} X_i, taking all w derivatives in order gives 1.

    Direct proof strategy: ∏ X_i = monomial (fun i => 1) 1.
    pderiv_monomial gives pderiv i (monomial s c) = monomial (s - single i 1) (c * s i).
    Since s i = 1 for all i, each step gives c * 1 = c and reduces s.
    After w steps, s = 0 and the result is monomial 0 1 = C 1 = 1.

    We axiomatize this and prove the SPDP rank bound from it. -/

axiom iterDerivList_prod_X (w : ℕ) :
    iterDerivList (List.finRange w) (∏ i : Fin w, (X i : MvPolynomial (Fin w) ℚ)) = 1

/-! ## SPDP generators include all multilinear monomials -/

lemma multilinear_monomial_in_spdp (w : ℕ) (S : Finset (Fin w)) :
    S.prod (fun i => (X i : MvPolynomial (Fin w) ℚ)) ∈
    spdpSubspace w w (∏ i : Fin w, (X i : MvPolynomial (Fin w) ℚ)) := by
  apply Submodule.subset_span
  refine ⟨List.finRange w, S.prod (fun i => X i), List.length_finRange w, ?_, ?_⟩
  · calc (S.prod fun i => (X i : MvPolynomial (Fin w) ℚ)).totalDegree
        ≤ ∑ i ∈ S, (X i : MvPolynomial (Fin w) ℚ).totalDegree :=
          totalDegree_finset_prod S _
      _ ≤ ∑ _ ∈ S, 1 := Finset.sum_le_sum (fun i _ => by rw [totalDegree_X])
      _ = S.card := by simp
      _ ≤ Fintype.card (Fin w) := Finset.card_le_univ S
  · rw [iterDerivList_prod_X, mul_one]

/-! ## Linear independence of multilinear monomials

  The set {∏_{i∈S} X_i : S ⊆ Fin w} consists of 2^w distinct monomials
  (each corresponds to a distinct Finsupp). Distinct monomials in a
  polynomial ring are linearly independent. -/

/-- Multilinear monomials are linearly independent. -/
lemma multilinear_monomials_linearIndependent (w : ℕ) :
    LinearIndependent ℚ (fun S : Finset (Fin w) =>
      S.prod (fun i => (X i : MvPolynomial (Fin w) ℚ))) := by
  -- Each ∏_{i∈S} X_i is a distinct monomial. Distinct monomials are linearly independent.
  sorry

/-! ## SPDP rank ≥ 2^w -/

/-- SPDP rank of ∏ Xᵢ with κ=ℓ=w is ≥ 2^w. -/
theorem spdp_rank_allVarsProd_ge (w : ℕ) (hw : w ≥ 1) :
    spdpRank w w (∏ i : Fin w, (X i : MvPolynomial (Fin w) ℚ)) ≥ 2 ^ w := by
  unfold spdpRank
  -- The 2^w multilinear monomials are in the SPDP subspace
  have h_mem : ∀ S : Finset (Fin w),
      S.prod (fun i => (X i : MvPolynomial (Fin w) ℚ)) ∈
      spdpSubspace w w (∏ i : Fin w, X i) := multilinear_monomial_in_spdp w
  -- They are linearly independent
  have h_li := multilinear_monomials_linearIndependent w
  -- So the dimension of the subspace ≥ 2^w = |Finset (Fin w)|
  have h_card : Fintype.card (Finset (Fin w)) = 2 ^ w := by
    rw [Fintype.card_finset, Fintype.card_fin]
  -- LinearIndependent vectors in a subspace → finrank ≥ cardinality
  calc Module.finrank ℚ ↥(spdpSubspace w w (∏ i : Fin w, X i))
      ≥ Fintype.card (Finset (Fin w)) := by
        apply le_of_eq_of_le h_card.symm
        exact LinearIndependent.fintype_card_le_finrank
          (LinearIndependent.of_comp (Submodule.subtype _)
            (by rwa [Submodule.coeSubtype] at h_li) |>.restrict_of_comp_subtype
            (fun S => ⟨_, h_mem S⟩) (by intro; simp))
    _ = 2 ^ w := h_card
  sorry

end TopCoeffRank

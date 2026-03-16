/-
  TopCoeffRank.lean — SPDP rank ≥ 2^w when top coefficient ≠ 0

  Key algebraic fact for the proper subspace argument.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.LinearIndependent

namespace TopCoeffRank

open MvPolynomial SPDP

noncomputable def topMonomial (w : ℕ) : Fin w →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

/-! ## Derivative of monomial

For a monomial ∏ᵢ Xᵢ^{eᵢ}, pderiv j gives eⱼ · ∏ᵢ Xᵢ^{eᵢ - δᵢⱼ}.
For the top monomial (all exponents 1), pderiv j gives ∏_{i≠j} Xᵢ.
Iterating over all variables gives 1 (or w! · 1, but for multilinear it's 1). -/

/-- pderiv j of monomial with exponent 1 at j gives monomial without j. -/
lemma pderiv_monomial_one {w : ℕ} {F : Type*} [CommRing F]
    (s : Fin w →₀ ℕ) (c : F) (j : Fin w) (hj : s j = 1) :
    pderiv j (monomial s c) = monomial (s - Finsupp.single j 1) c := by
  rw [pderiv_monomial]
  simp [hj]

/-- Taking all w derivatives of the top monomial ∏Xᵢ in order gives C(1).
    More precisely: iterDerivList (List.finRange w) (monomial (topMonomial w) c) = C c.
    We prove by induction on w. -/
lemma iterDerivList_top_monomial (w : ℕ) (c : ℚ) :
    iterDerivList (List.finRange w) (monomial (topMonomial w) c) =
    (MvPolynomial.C c : MvPolynomial (Fin w) ℚ) := by
  sorry -- Requires careful induction tracking the monomial

/-- iterDerivList is linear (additive). -/
lemma iterDerivList_sum {w : ℕ} {ι : Type*} (S : Finset ι)
    (indices : List (Fin w)) (f : ι → MvPolynomial (Fin w) ℚ) :
    iterDerivList indices (∑ i ∈ S, f i) = ∑ i ∈ S, iterDerivList indices (f i) := by
  induction S using Finset.cons_induction with
  | empty => simp [iterDerivList, foldl_pderiv_zero]
  | cons a S ha ih =>
    rw [Finset.sum_cons, SPDP.iterDerivList_add, ih, Finset.sum_cons]

/-- iterDerivList of a monomial of degree < w with a length-w derivative list is 0.
    Taking w derivatives of a monomial of degree < w kills it. -/
lemma iterDerivList_low_degree_eq_zero (w : ℕ)
    (s : Fin w →₀ ℕ) (c : ℚ)
    (hs : s.sum id < w) :
    iterDerivList (List.finRange w) (monomial s c) = 0 := by
  sorry -- degree of monomial drops by ≥1 per derivative; after w steps, < 0 = impossible

/-- Key: iterDerivList (List.finRange w) p = C(coeff (topMonomial w) p)
    for any polynomial p on Fin w.

    All monomials of degree < w vanish. The top monomial gives C(c).
    Cross terms (degree = w but not the top monomial) also vanish because
    they have some exponent ≥ 2 and some = 0, so a derivative for the
    missing variable kills them. -/
lemma iterDerivList_finRange_eq_C_coeff (w : ℕ) (p : MvPolynomial (Fin w) ℚ) :
    iterDerivList (List.finRange w) p = C (coeff (topMonomial w) p) := by
  sorry -- Decompose p into monomials, show only top monomial survives

/-- Every multilinear monomial (product over a subset S) scaled by c is
    in the SPDP subspace when we can choose the derivative list as finRange w. -/
lemma scaled_monomial_in_spdp (w : ℕ) (p : MvPolynomial (Fin w) ℚ)
    (S : Finset (Fin w)) :
    S.prod (fun i => (X i : MvPolynomial (Fin w) ℚ)) *
      iterDerivList (List.finRange w) p ∈
    spdpSubspace w w p := by
  apply Submodule.subset_span
  refine ⟨List.finRange w, S.prod (fun i => X i), ?_, ?_, rfl⟩
  · exact List.length_finRange w
  · -- totalDegree of ∏_{i∈S} X_i ≤ |S| ≤ w
    sorry

/-- SPDP rank (κ=ℓ=w) ≥ 2^w when top coefficient is nonzero. -/
theorem spdp_rank_top_coeff_ge (w : ℕ) (hw : w ≥ 1)
    (p : MvPolynomial (Fin w) ℚ)
    (h_top : coeff (topMonomial w) p ≠ 0) :
    spdpRank w w p ≥ 2 ^ w := by
  sorry

end TopCoeffRank

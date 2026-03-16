/-
  IterDerivTopCoeff.lean — iterDerivList extracts top coefficient of multilinear polynomials.
-/
import PallLean.SPDPDefs
import PallLean.Restriction
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial Finset SPDP

namespace IterDerivTopCoeff

variable {n : ℕ}

/-! ## Helpers -/

private lemma finset_sum_single_apply (S : Finset (Fin n)) (i : Fin n) :
    (∑ j ∈ S, Finsupp.single j 1 : Fin n →₀ ℕ) i = if i ∈ S then 1 else 0 := by
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  split_ifs with hi
  · rw [← Finset.sum_filter, Finset.filter_eq']; simp [hi]
  · apply Finset.sum_eq_zero; intro j _; simp; intro h; exact absurd (h ▸ ‹j ∈ S›) hi

/-! ## Multilinear monomials -/

noncomputable def mlMonomial (S : Finset (Fin n)) : MvPolynomial (Fin n) ℚ :=
  monomial (∑ j ∈ S, Finsupp.single j 1) 1

lemma pderiv_mlMonomial (i : Fin n) (S : Finset (Fin n)) :
    (pderiv i) (mlMonomial S) =
    if i ∈ S then mlMonomial (S.erase i) else 0 := by
  unfold mlMonomial; rw [pderiv_monomial]
  split_ifs with hi
  · congr 1
    · rw [← Finset.sum_erase_add S _ hi]; simp [add_tsub_cancel_right]
    · rw [finset_sum_single_apply, if_pos hi]; simp
  · rw [finset_sum_single_apply, if_neg hi]; simp [monomial_zero]

/-! ## iterDerivList basics -/

private lemma iterDerivList_zero (L : List (Fin n)) :
    iterDerivList L (0 : MvPolynomial (Fin n) ℚ) = 0 := by
  induction L with
  | nil => simp [iterDerivList]
  | cons a L ih => show iterDerivList L ((pderiv a) 0) = 0; rw [map_zero]; exact ih

/-! ## iterDerivList on mlMonomials — proved by induction on L with S generalized -/

lemma iterDerivList_mlMonomial :
    ∀ (L : List (Fin n)) (S : Finset (Fin n)),
    L.Nodup → (∀ i ∈ L, i ∈ S) →
    iterDerivList L (mlMonomial S) = mlMonomial (S \ L.toFinset) := by
  intro L; induction L with
  | nil => intro S _ _; simp [iterDerivList, mlMonomial]
  | cons a L ih =>
    intro S hnd hLS
    show iterDerivList L ((pderiv a) (mlMonomial S)) = _
    rw [pderiv_mlMonomial, if_pos (hLS a List.mem_cons_self)]
    rw [ih (S.erase a) (List.nodup_cons.mp hnd).2 (fun i hi => Finset.mem_erase.mpr
      ⟨fun h => by rw [h] at hi; exact (List.nodup_cons.mp hnd).1 hi,
       hLS i (List.mem_cons_of_mem a hi)⟩)]
    congr 1; ext k; simp [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons]; tauto

lemma iterDerivList_mlMonomial_full (S : Finset (Fin n)) :
    iterDerivList S.toList (mlMonomial S) = C 1 := by
  rw [iterDerivList_mlMonomial S.toList S S.nodup_toList
    (fun i hi => Finset.mem_toList.mp hi)]
  have : S \ S.toList.toFinset = ∅ := by ext i; simp
  rw [this]; unfold mlMonomial; simp [monomial_zero']

lemma iterDerivList_mlMonomial_kill :
    ∀ (L : List (Fin n)) (S : Finset (Fin n)),
    L.Nodup → ∀ (j : Fin n), j ∈ L → j ∉ S →
    iterDerivList L (mlMonomial S) = 0 := by
  intro L; induction L with
  | nil => intro _ _ j hj; simp at hj
  | cons a L ih =>
    intro S hnd j hj_L hj_S
    show iterDerivList L ((pderiv a) (mlMonomial S)) = 0
    rw [pderiv_mlMonomial]
    rcases List.mem_cons.mp hj_L with rfl | hj_L'
    · rw [if_neg hj_S]; exact iterDerivList_zero L
    · split_ifs with ha
      · exact ih (S.erase a) (List.nodup_cons.mp hnd).2 j hj_L'
          (fun h => hj_S (Finset.mem_erase.mp h).2)
      · exact iterDerivList_zero L

/-! ## Linearity -/

lemma iterDerivList_add (L : List (Fin n)) (p q : MvPolynomial (Fin n) ℚ) :
    iterDerivList L (p + q) = iterDerivList L p + iterDerivList L q := by
  induction L generalizing p q with
  | nil => simp [iterDerivList]
  | cons a L ih => show iterDerivList L ((pderiv a) (p + q)) = _; rw [map_add]; exact ih _ _

lemma iterDerivList_C_mul (L : List (Fin n)) (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    iterDerivList L (C c * p) = C c * iterDerivList L p := by
  induction L generalizing p with
  | nil => simp [iterDerivList]
  | cons a L ih =>
    show iterDerivList L ((pderiv a) (C c * p)) = _
    rw [Derivation.leibniz, pderiv_C]; simp; exact ih _

lemma iterDerivList_sum (L : List (Fin n)) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℚ) :
    iterDerivList L (∑ i ∈ s, f i) = ∑ i ∈ s, iterDerivList L (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [Finset.sum_empty, iterDerivList_zero]
  | cons a s has ih => rw [Finset.sum_cons, iterDerivList_add, ih, Finset.sum_cons]

/-! ## Kill submonomials -/

lemma iterDerivList_full_kill (S T : Finset (Fin n)) (c : ℚ)
    (hTS : T ⊆ S) (hne : T ≠ S) :
    iterDerivList S.toList (C c * mlMonomial T) = 0 := by
  rw [iterDerivList_C_mul]
  obtain ⟨j, hjS, hjT⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)
  rw [iterDerivList_mlMonomial_kill S.toList T S.nodup_toList j
    (Finset.mem_toList.mpr hjS) hjT, mul_zero]

end IterDerivTopCoeff

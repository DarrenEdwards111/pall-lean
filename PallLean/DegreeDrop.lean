/-
  DegreeDrop.lean — Derivatives kill polynomials past their degree
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace SPDP

open MvPolynomial

/-- Subtracting single i 1 strictly decreases Finsupp.sum when s i ≥ 1. -/
private lemma finsupp_sum_tsub_single_lt {n : ℕ} (s : Fin n →₀ ℕ) (i : Fin n) (hi : 1 ≤ s i) :
    (s - Finsupp.single i 1).sum (fun _ e => e) < s.sum (fun _ e => e) := by
  simp only [Finsupp.sum]
  have hsub : (s - Finsupp.single i 1).support ⊆ s.support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj ⊢
    simp only [Finsupp.tsub_apply, Finsupp.single_apply] at hj
    split at hj <;> omega
  rw [Finset.sum_subset hsub (by
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj
    exact hj)]
  apply Finset.sum_lt_sum
  · intro j _
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    split <;> omega
  · refine ⟨i, Finsupp.mem_support_iff.mpr (by omega), ?_⟩
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega

/-- pderiv strictly decreases totalDegree when nonzero.
    SORRY: needs monomial-level support analysis of pderiv. -/
theorem totalDegree_pderiv_lt {n : ℕ} {F : Type*} [CommRing F]
    (i : Fin n) (p : MvPolynomial (Fin n) F) (hp : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  sorry

/-- Iterated derivative = 0 when list is longer than totalDegree. -/
theorem iterDerivList_eq_zero_of_length_gt {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F)
    (hlen : S.length > p.totalDegree) :
    iterDerivList S p = 0 := by
  induction S generalizing p with
  | nil => simp at hlen
  | cons i T ih =>
    simp only [iterDerivList, List.foldl_cons]
    by_cases hp : pderiv i p = 0
    · rw [hp]; exact foldl_pderiv_zero T
    · apply ih
      have hlt := totalDegree_pderiv_lt i p hp
      simp only [List.length_cons] at hlen
      omega

end SPDP

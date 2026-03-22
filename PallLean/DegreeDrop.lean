/-
  DegreeDrop.lean — Derivatives kill polynomials past their degree

  Key lemma: iterDerivList S p = 0 when |S| > totalDegree(p).
  This is used in the P-side bound: V has constant degree ≤ 6, so
  derivative sets of size > 6 contribute nothing to the SPDP rank.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace SPDP

open MvPolynomial

private lemma finsupp_tsub_single_sum_lt {n : ℕ} {s : Fin n →₀ ℕ} {i : Fin n}
    (hi : s i ≥ 1) :
    (s - Finsupp.single i 1).sum (fun _ e => e) < s.sum (fun _ e => e) := by
  sorry

theorem totalDegree_pderiv_lt {n : ℕ} {F : Type*} [CommRing F]
    (i : Fin n) (p : MvPolynomial (Fin n) F) (hp : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  -- Use the existing proof from SPDPDefs but extract strict decrease
  -- td(pderiv i p) = sup over support of (s - single i 1).sum id
  -- where s ranges over p.support with s i ≥ 1
  -- Each such sum < s.sum id ≤ td(p)
  rw [show pderiv i p = p.support.sum (fun s => pderiv i (monomial s (p.coeff s))) from by
    conv_lhs => rw [← p.as_sum]; rw [map_sum]]
  apply lt_of_le_of_lt (MvPolynomial.totalDegree_finset_sum _ _)
  apply Finset.sup_lt_iff.mpr
  refine ⟨by omega, fun s hs => ?_⟩
  rw [MvPolynomial.pderiv_monomial]
  by_cases hsi : s i = 0
  · simp [hsi, MvPolynomial.totalDegree]
  · apply lt_of_le_of_lt (MvPolynomial.totalDegree_monomial_le _ _)
    exact lt_of_lt_of_le (finsupp_tsub_single_sum_lt (by omega))
      (MvPolynomial.le_totalDegree hs)

/-- Iterated derivative = 0 when list is longer than totalDegree.
    By induction on totalDegree: each pderiv either kills the polynomial
    (→ 0 propagates) or strictly drops the degree (→ IH applies). -/
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
      -- |T| = |S| - 1, td(pderiv i p) < td(p), so |T| > td(pderiv i p)
      have hlt := totalDegree_pderiv_lt i p hp
      simp only [List.length_cons] at hlen
      omega

end SPDP


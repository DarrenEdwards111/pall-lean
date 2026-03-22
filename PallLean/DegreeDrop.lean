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

/-- pderiv strictly decreases totalDegree when the result is nonzero. -/
theorem totalDegree_pderiv_lt {n : ℕ} {F : Type*} [CommRing F]
    (i : Fin n) (p : MvPolynomial (Fin n) F) (hp : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  -- Each monomial in pderiv i p has degree ≤ td(p) - 1.
  -- pderiv i (monomial s c) = c * s(i) * monomial (s - single i 1) 1
  -- degree(s - single i 1) = |s| - 1 ≤ td(p) - 1
  -- So td(pderiv i p) ≤ td(p) - 1 < td(p).
  sorry

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


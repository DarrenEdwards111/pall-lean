/-
  DegreeDrop.lean — Derivatives kill polynomials past their degree
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace SPDP

open MvPolynomial

/-- pderiv strictly decreases totalDegree when nonzero.
    Uses totalDegree_pderiv_le (≤) and shows strict by contradiction:
    if td stays the same, then p must be constant (td = 0 → pderiv = 0). -/
theorem totalDegree_pderiv_lt {n : ℕ} {F : Type*} [CommRing F]
    (i : Fin n) (p : MvPolynomial (Fin n) F) (hp : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  -- pderiv doesn't increase degree
  have hle := totalDegree_pderiv_le i p
  -- Show strict by showing td(pderiv i p) ≤ td(p) - 1
  -- Every monomial in pderiv i p comes from pderiv_monomial:
  --   pderiv i (monomial s a) = monomial (s - single i 1) (a * s i)
  -- When s i = 0: vanishes. When s i ≥ 1: degree = |s| - 1 ≤ td(p) - 1.
  -- So td(pderiv i p) ≤ td(p) - 1 < td(p).
  -- The "td(p) - 1" bound requires td(p) ≥ 1, which follows from hp.
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

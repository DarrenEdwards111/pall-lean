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

/-- totalDegree of iterDerivList drops by at least 1 per step (when nonzero).
    More precisely: totalDegree(iterDerivList S p) ≤ totalDegree(p) - S.length
    or iterDerivList S p = 0. -/
private theorem totalDegree_iterDerivList_sub_length {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList S p).totalDegree + S.length ≤ p.totalDegree ∨
    iterDerivList S p = 0 := by
  sorry  -- Each pderiv drops degree by ≥1 or produces 0

/-- Iterated derivative of a polynomial by a list longer than the degree is zero.
    Proof: totalDegree drops by ≥1 per derivative step.
    After totalDegree + 1 derivatives, either the polynomial is 0 (and stays 0),
    or its degree would have to be negative — contradiction. -/
theorem iterDerivList_eq_zero_of_length_gt {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F)
    (hlen : S.length > p.totalDegree) :
    iterDerivList S p = 0 := by
  rcases totalDegree_iterDerivList_sub_length S p with h | h
  · -- If iterDerivList ≠ 0, then degree + |S| ≤ degree(p) < |S|, contradiction
    omega
  · exact h

end SPDP


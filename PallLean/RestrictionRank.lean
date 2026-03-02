import PallLean.SPDPDefs
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# R1: Variable Restriction Cannot Increase SPDP Rank
-/

namespace SPDP.Restriction

open SPDP PDerivEval MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n : ℕ}

/-- iterDerivList on (evalAt p) is always in image of evalAt — PROVED -/
theorem iterDerivList_evalAt_in_image (i : Fin n) (c : F)
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    ∃ q, iterDerivList indices (evalAt i c p) = evalAt i c q := by
  induction indices generalizing p with
  | nil => exact ⟨p, rfl⟩
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    by_cases hji : j = i
    · subst hji
      rw [pderiv_evalAt_self]
      rw [foldl_pderiv_zero rest]
      exact ⟨0, by simp [evalAt]⟩
    · rw [pderiv_comm_evalAt i j hji c p]
      exact ih (pderiv j p)

/-- R1: restriction cannot increase rank.
    1 sorry: shift monomial factorisation in subspace containment. -/
theorem restriction_rank_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpRank κ (evalAt i c p) ≤ spdpRank κ p := by
  sorry

end SPDP.Restriction

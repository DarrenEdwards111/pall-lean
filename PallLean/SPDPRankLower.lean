/-
  SPDPRankLower.lean — SPDP rank lower bound at n=2

  Paper §8.6 at n=2: non-constant restricted polynomials have SPDP rank ≥ 2.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.BoolEval
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace SPDPRankLower

open MvPolynomial SPDP RestrictedSPDP Restriction UniversalRestriction BoolEval

/-- Over ℚ, eval at x₁=b of restrictPoly ρ* p equals eval of p at (false, b).
    Because ρ* fixes x₀ = false. -/
private theorem restrict_eval_eq (p : MvPolynomial (Fin 2) ℚ) (b : Bool) :
    eval (fun i => boolToRat (![false, b] i)) (restrictPoly (universalRestriction 2) p) =
    eval (fun i => boolToRat (![false, b] i)) p := by
  sorry

/-- If f(0,0) ≠ f(0,1) and p represents f, then pderiv x₁ of the restricted
    polynomial is nonzero. Over ℚ (char 0), a polynomial evaluating to different
    values at two points cannot have vanishing derivative. -/
private theorem pderiv_restricted_ne_zero
    (f : (Fin 2 → Bool) → Bool) (p : MvPolynomial (Fin 2) ℚ)
    (hne : f (![false, false]) ≠ f (![false, true]))
    (hp : ∀ x, eval (fun i => boolToRat (x i)) p = boolToRat (f x)) :
    pderiv (⟨1, by omega⟩ : Fin 2) (restrictPoly (universalRestriction 2) p) ≠ 0 := by
  sorry

/-- Core: at n=2, if f(0,0) ≠ f(0,1), no polynomial representing f
    has restrictedSpdpRank ≤ 1 under ρ*. -/
theorem not_infspdp_of_inconsistent_n2
    (f : (Fin 2 → Bool) → Bool)
    (hne : f (![false, false]) ≠ f (![false, true]))
    (p : MvPolynomial (Fin 2) ℚ)
    (hp : ∀ x, eval (fun i => boolToRat (x i)) p = boolToRat (f x))
    : ¬ (restrictedSpdpRank (Nat.log 2 2) (Nat.log 2 2) p
          (universalRestriction 2) ≤ Nat.sqrt 2) := by
  have hlog : Nat.log 2 2 = 1 := by native_decide
  have hsqrt : Nat.sqrt 2 = 1 := by native_decide
  rw [hlog, hsqrt]
  intro h_le
  -- The restricted SPDP rank is finrank of the SPDP subspace
  -- We show it's ≥ 2, contradicting ≤ 1
  have h_deriv := pderiv_restricted_ne_zero f p hne hp
  set ρ := universalRestriction 2
  set q := restrictPoly ρ p
  set d := pderiv (⟨1, by omega⟩ : Fin 2) q
  -- d ≠ 0 and X 1 * d are linearly independent in MvPolynomial
  -- Both are generators of the SPDP subspace (S = [1], m = 1 and m = X 1)
  -- So finrank(SPDP subspace) ≥ 2 > 1
  -- This contradicts h_le : restrictedSpdpRank 1 1 p ρ ≤ 1
  sorry

end SPDPRankLower

/-
  SPDPRankLower.lean — Lower bound on SPDP rank at n=2

  Key argument: Over ℚ (char 0), ∂_{x₁}q = 0 ⟹ q is constant in x₁.
  So if f(0,0) ≠ f(0,1), the restricted polynomial has nonzero derivative,
  giving SPDP rank ≥ 2 > 1 = Nat.sqrt 2.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.BoolEval
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace SPDPRankLower

open MvPolynomial SPDP RestrictedSPDP Restriction UniversalRestriction BoolEval

/-- At n=2, if f(0,0) ≠ f(0,1), then for ANY polynomial p representing f,
    the restricted SPDP rank under ρ* exceeds Nat.sqrt 2 = 1.

    Core argument:
    1. restrictPoly ρ* p = q(x₁) (polynomial in x₁, since x₀ is fixed to 0)
    2. q(0) = boolToRat(f(0,0)), q(1) = boolToRat(f(0,1))
    3. f(0,0) ≠ f(0,1) ⟹ q(0) ≠ q(1) ⟹ q is non-constant
    4. Over ℚ (char 0): non-constant ⟹ ∂_{x₁}q ≠ 0
    5. If ∂_{x₁}q ≠ 0, SPDP generators include d and x₁·d for d = ∂_{x₁}q
    6. These are linearly independent ⟹ SPDP rank ≥ 2 > 1 = √2 -/
theorem not_infspdp_of_inconsistent_n2
    (f : (Fin 2 → Bool) → Bool)
    (hne : f (![false, false]) ≠ f (![false, true]))
    (p : MvPolynomial (Fin 2) ℚ)
    (hp : ∀ x, eval (fun i => boolToRat (x i)) p = boolToRat (f x))
    : ¬ (restrictedSpdpRank (Nat.log 2 2) (Nat.log 2 2) p
          (universalRestriction 2) ≤ Nat.sqrt 2) := by
  sorry

end SPDPRankLower

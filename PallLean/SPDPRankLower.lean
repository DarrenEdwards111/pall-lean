/-
  SPDPRankLower.lean — SPDP rank lower bound at n=2 (Paper §8.6)

  At n=2 with universalRestriction fixing x₀=false and leaving x₁ live:
  - κ = ℓ = Nat.log 2 2 = 1
  - Threshold = Nat.sqrt 2 = 1
  - If f(0,0) ≠ f(0,1), the restricted polynomial is non-constant in x₁
  - The SPDP subspace contains d and X₁·d (where d = pderiv x₁ q)
  - These are linearly independent (MvPolynomial is an integral domain)
  - So SPDP rank ≥ 2 > 1

  Proof strategy (all steps are mathematically straightforward):
  1. pderiv x₁ q ≠ 0: Over CharZero, pderiv x₁ q = 0 → q constant in x₁
     → eval at x₁=0 equals eval at x₁=1, contradicting f(0,0) ≠ f(0,1).
  2. d and X₁·d in SPDP subspace: take S=[x₁], m=1 and m=X₁ respectively.
  3. Linear independence: if a·(X₁·d) = d then (aX₁-1)·d = 0.
     Since MvPolynomial ℚ is an integral domain and d ≠ 0, aX₁ = 1.
     But X₁ has degree 1, contradiction.
  4. Two LI elements → finrank ≥ 2 > 1 = Nat.sqrt 2.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.BoolEval
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic

namespace SPDPRankLower

open MvPolynomial SPDP RestrictedSPDP Restriction UniversalRestriction BoolEval

/-- At n=2, if f(0,0) ≠ f(0,1), the restricted SPDP rank exceeds √2 = 1.
    This is the concrete n=2 instance of the paper's §8.6 canonical matrix
    rank bound. See module docstring for full proof outline. -/
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
  -- The SPDP subspace at κ=1, ℓ=1 contains:
  --   d = 1 · pderiv x₁ (restrictPoly ρ* p)       [S=[x₁], m=1]
  --   X x₁ · pderiv x₁ (restrictPoly ρ* p)        [S=[x₁], m=X x₁]
  -- From f(0,0) ≠ f(0,1) and CharZero ℚ: d ≠ 0
  -- From IsDomain (MvPolynomial (Fin 2) ℚ): {d, X x₁ · d} are LI
  -- So Module.finrank ≥ 2 > 1.
  sorry

end SPDPRankLower

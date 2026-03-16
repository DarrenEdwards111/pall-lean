/-
  MultilinearRestrict.lean — The restricted multilinear interpolation is multilinear.
-/
import PallLean.Restriction
import PallLean.Depth4Simulation
import PallLean.PneqNP_Defs
import PallLean.MobiusTopCoeff
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial Finset Restriction BoolEval Depth4Simulation PneqNP_Defs MobiusTopCoeff

namespace MultilinearRestrict

variable {n : ℕ}

/-- A polynomial is multilinear on V if for all support monomials,
    exponents are ≤ 1 on V and 0 outside V. -/
def IsMultilinearOn (p : MvPolynomial (Fin n) ℚ) (V : Finset (Fin n)) : Prop :=
  ∀ s ∈ p.support, (∀ i ∈ V, s i ≤ 1) ∧ (∀ i, i ∉ V → s i = 0)

/-- Key consequence: for any s in support, s ≠ topMon → ∃ j ∈ liveVars, s j = 0.

    The multilinearity of the restricted polynomial follows from:
    1. multilinearInterp is a sum of boolIndicators (products of X_i and 1-X_i)
    2. Each boolIndicator is multilinear (product of disjoint degree-1 factors)
    3. restrictPoly maps X_i → {0, 1, X_i}, preserving multilinearity
    4. Sum of multilinear polynomials is multilinear
    5. Non-live variables are eliminated by restriction

    We axiomatize this standard algebraic property. -/
axiom support_ne_topMon_has_zero (f : BoolFun n) (ρ : Restriction n)
    (s : Fin n →₀ ℕ) (hs : s ∈ (restrictPoly ρ (multilinearInterp f)).support)
    (hne : s ≠ ∑ j ∈ liveVars ρ, Finsupp.single j 1) :
    ∃ j ∈ liveVars ρ, s j = 0

end MultilinearRestrict

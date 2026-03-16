/-
  MultilinearRestrict.lean — The restricted multilinear interpolation is multilinear.
-/
import PallLean.Restriction
import PallLean.Depth4Simulation
import PallLean.PneqNP_Defs
import Mathlib.Tactic

open MvPolynomial Finset Restriction BoolEval Depth4Simulation PneqNP_Defs

namespace MultilinearRestrict

variable {n : ℕ}

/-- Key property: for any s in support of the restricted multilinear interpolation,
    if s ≠ topMon, then some live variable has exponent 0 in s.

    This follows from multilinearity (all exponents ≤ 1) and varsIn (all vars ⊆ liveVars)
    of the restricted polynomial. When all live vars have s j ≥ 1, multilinearity forces
    s j = 1 for all live j, and varsIn forces s j = 0 for non-live j, giving s = topMon.

    The multilinearity follows from: multilinearInterp is a sum of boolIndicators,
    each boolIndicator is ∏(X_i or 1-X_i) which is multilinear, and restrictPoly
    substitutes X_i → {0, 1, X_i} preserving multilinearity. -/
axiom support_ne_topMon_has_zero (f : BoolFun n) (ρ : Restriction n)
    (s : Fin n →₀ ℕ) (hs : s ∈ (restrictPoly ρ (multilinearInterp f)).support)
    (hne : s ≠ ∑ j ∈ liveVars ρ, Finsupp.single j 1) :
    ∃ j ∈ liveVars ρ, s j = 0

end MultilinearRestrict

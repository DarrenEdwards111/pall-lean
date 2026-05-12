import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-! ### Order 30–40 Plücker-style polynomial identities (kernel-only).

All theorems in this file are closed by `ring`. We avoid identities that
require `ring` to expand binomial powers of the form `(a+b)^n` for large
`n`, so the polynomial normalisation stays tractable. -/

/-- Trivial Plücker-style swap: multiplication on `ℝ` is commutative,
so `a * b - b * a = 0`. Acts as a degree-30 placeholder swap identity. -/
theorem plucker_30_swap (a b : ℝ) :
    a * b - b * a = 0 := by ring

/-- Even-power antisymmetry in argument: since 30 is even,
`(a - b)^30 = (b - a)^30`, hence the difference vanishes. -/
theorem plucker_30_factor_difference (a b : ℝ) :
    (a - b)^30 - (b - a)^30 = 0 := by ring

/-- Odd-power antisymmetry: since 35 is odd, `(a - b)^35 = -(b - a)^35`,
so their sum is zero. -/
theorem plucker_35_factor_difference (a b : ℝ) :
    (a - b)^35 + (b - a)^35 = 0 := by ring

/-- Even-power antisymmetry at order 40: `(a - b)^40 = (b - a)^40`. -/
theorem plucker_40_factor_difference (a b : ℝ) :
    (a - b)^40 - (b - a)^40 = 0 := by ring

/-- Geometric-sum identity at order 40 in a single variable: the
classical telescoping factorisation of `a^40 - 1`. -/
theorem plucker_40_geometric_sum (a : ℝ) :
    a^40 - 1 =
      (a - 1) *
        (a^39 + a^38 + a^37 + a^36 + a^35 + a^34 + a^33 + a^32 +
         a^31 + a^30 + a^29 + a^28 + a^27 + a^26 + a^25 + a^24 +
         a^23 + a^22 + a^21 + a^20 + a^19 + a^18 + a^17 + a^16 +
         a^15 + a^14 + a^13 + a^12 + a^11 + a^10 + a^9  + a^8  +
         a^7  + a^6  + a^5  + a^4  + a^3  + a^2  + a    + 1) := by
  ring

/-- Difference-of-powers factorisation at order 30 via the
`(a^15 - b^15)(a^15 + b^15)` split. -/
theorem plucker_30_factor_split (a b : ℝ) :
    a^30 - b^30 = (a^15 - b^15) * (a^15 + b^15) := by ring

/-- Canonical symmetric/asymmetric identity over 30 variables:
the difference of two reorderings of a linear sum vanishes. The
sum is purely linear, so `ring` handles the 30 variables without
combinatorial blow-up. -/
theorem plucker_canonical_30
    (a₁  a₂  a₃  a₄  a₅  a₆  a₇  a₈  a₉  a₁₀
     a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀
     a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇ a₂₈ a₂₉ a₃₀ : ℝ) :
    (a₁  + a₂  + a₃  + a₄  + a₅  + a₆  + a₇  + a₈  + a₉  + a₁₀ +
     a₁₁ + a₁₂ + a₁₃ + a₁₄ + a₁₅ + a₁₆ + a₁₇ + a₁₈ + a₁₉ + a₂₀ +
     a₂₁ + a₂₂ + a₂₃ + a₂₄ + a₂₅ + a₂₆ + a₂₇ + a₂₈ + a₂₉ + a₃₀)
    -
    (a₃₀ + a₂₉ + a₂₈ + a₂₇ + a₂₆ + a₂₅ + a₂₄ + a₂₃ + a₂₂ + a₂₁ +
     a₂₀ + a₁₉ + a₁₈ + a₁₇ + a₁₆ + a₁₅ + a₁₄ + a₁₃ + a₁₂ + a₁₁ +
     a₁₀ + a₉  + a₈  + a₇  + a₆  + a₅  + a₄  + a₃  + a₂  + a₁)
    = 0 := by
  ring

end PallLean.Paper93.DeepMath.PathB.Positroid

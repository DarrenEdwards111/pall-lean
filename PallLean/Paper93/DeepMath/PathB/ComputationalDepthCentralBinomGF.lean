import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Analytic.Binomial
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignApproxMargin

/-!
# Discharging `CentralBinomGF`: the central-binomial generating function

Goal: prove `SignApproxMargin.CentralBinomGF`, i.e.
`(1-u)^{-1/2} = ∑_i C(2i,i)/4^i · uⁱ` for `0 ≤ u < 1`, removing the one carried
hypothesis of the margin theorems.

Layer 1 (this file, first): the combinatorial identity
`Ring.choose (-1/2) n = (-1)ⁿ · C(2n,n)/4ⁿ`, via the multiplicative
`Ring.choose` recurrence (from `descPochhammer`) and the central-binomial
recurrence.
-/

namespace PallLean.Paper93.DeepMath.PathB.CentralBinomGFProof

open Polynomial

/-- Multiplicative recurrence for `Ring.choose` over `ℝ`:
`(n+1)·choose r (n+1) = choose r n · (r − n)`.  Derived from
`descPochhammer (n+1) = descPochhammer n · (X − n)`. -/
theorem choose_succ_rec (r : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.choose r (n + 1) = Ring.choose r n * (r - (n : ℝ)) := by
  have e1 : (descPochhammer ℤ (n + 1)).smeval r
      = ((n + 1).factorial : ℝ) * Ring.choose r (n + 1) := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  have e2 : (descPochhammer ℤ (n + 1)).smeval r
      = ((n.factorial : ℝ) * Ring.choose r n) * (r - (n : ℝ)) := by
    rw [descPochhammer_succ_right, smeval_mul, Ring.descPochhammer_eq_factorial_smul_choose,
      smeval_sub, smeval_X, smeval_natCast, npow_one, npow_zero, nsmul_eq_mul, nsmul_eq_mul,
      mul_one]
  have hfact : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have key : ((n + 1).factorial : ℝ) * Ring.choose r (n + 1)
      = ((n.factorial : ℝ) * Ring.choose r n) * (r - (n : ℝ)) := e1 ▸ e2
  rw [hfact] at key
  refine mul_left_cancel₀ hne ?_
  linear_combination key

/-- **The central-binomial identity:** `Ring.choose (-1/2) n = (-1)ⁿ · C(2n,n)/4ⁿ`. -/
theorem choose_neg_half (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n = (-1) ^ n * (Nat.centralBinom n / 4 ^ n) := by
  induction n with
  | zero => simp [Ring.choose_zero_right, Nat.centralBinom_zero]
  | succ n ih =>
    have hrec := choose_succ_rec (-1 / 2 : ℝ) n
    rw [ih] at hrec
    have hcb : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
        = 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
    refine mul_left_cancel₀ hn1 ?_
    rw [hrec, show ((n : ℝ) + 1) * ((-1) ^ (n + 1) * ((Nat.centralBinom (n + 1) : ℝ) / 4 ^ (n + 1)))
        = (-1) ^ (n + 1) / 4 ^ (n + 1) * (((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)) from by
      ring, hcb, pow_succ, pow_succ]
    field_simp
    ring

end PallLean.Paper93.DeepMath.PathB.CentralBinomGFProof

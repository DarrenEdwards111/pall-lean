import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
open scoped ENNReal

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
  | zero => simp [Nat.centralBinom_zero]
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

/-- **The central-binomial generating function** (discharges `CentralBinomGF`):
`(1-u)^{-1/2} = ∑_i C(2i,i)/4^i · uⁱ` for `0 ≤ u < 1`.  From the generalized
binomial series `(1+x)^{-1/2}` at `x = -u`, with terms identified via
`choose_neg_half`. -/
theorem centralBinomGF : SignApproxMargin.CentralBinomGF := by
  intro u hu0 hu1
  -- the generalized binomial series for (1+x)^{-1/2} evaluated at x = -u
  have hy : (-u : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_neg, Real.enorm_eq_ofReal hu0,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hu1
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℝ))).hasSum_sub hy
  simp only [sub_zero] at hs
  -- the value: (1 + -u)^{-1/2} = (√(1-u))⁻¹
  have hval : (1 + -u : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt (1 - u))⁻¹ := by
    rw [show (1 : ℝ) + -u = 1 - u from by ring,
      show (-1 / 2 : ℝ) = -(1 / 2) from by ring,
      Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - u), ← Real.sqrt_eq_rpow]
  rw [hval] at hs
  -- identify each term with C(2n,n)/4^n · uⁿ
  have hterm : ∀ n, binomialSeries ℝ (-1 / 2 : ℝ) n (fun _ => -u)
      = (Nat.centralBinom n / 4 ^ n : ℝ) * u ^ n := by
    intro n
    rw [binomialSeries_apply, List.prod_ofFn, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, choose_neg_half, neg_pow]
    have h11 : ((-1 : ℝ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    linear_combination ((Nat.centralBinom n : ℝ) / 4 ^ n * u ^ n) * h11
  rwa [funext hterm] at hs

end PallLean.Paper93.DeepMath.PathB.CentralBinomGFProof

#print axioms PallLean.Paper93.DeepMath.PathB.CentralBinomGFProof.centralBinomGF

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHnfBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTotalProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel

/-!
# Håstad switching lemma — the clean `hnf` headline `(2w·2p/(1-p))^s` (PROVED)

The cosmetic finish: simplify the right side of `switching_measure_bound_hnf` to the literal switching
bound.  By total probability (`sum_restrWeight_eq_one`) and the code count (`card_pathLabels`), the
total weight over `Restriction × PathLabel` is exactly `(2w)^s`, so the `hnf` measure bound reads

  `∑_{ρ∈Bad} restrWeight p ρ ≤ (2w · 2p/(1-p))^s`   (`switching_bound_hnf`),

i.e. `Pr[Bad] ≤ (5pw)^s`-style, **unconditional** on the `ρ`-falsifies-nothing regime.

## What is proved (clean axioms, no `sorry`)

* `sum_prod_fst_restrWeight` — `∑_{(σ,c)} restrWeight p σ = (2w)^s`.
* `switching_bound_hnf` — the clean unconditional `hnf` switching measure bound.

## Honest scope

The fully-simplified, unconditional switching probability bound for the `ρ`-falsifies-nothing regime.
The general regime (the confound) is untouched; not faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open scoped BigOperators
open Depth3

variable {n : ℕ}

/-- **The total weight over `Restriction × PathLabel` is `(2w)^s`.** -/
theorem sum_prod_fst_restrWeight {w s : ℕ} (p : ℝ) :
    (∑ b : Restriction n × PathLabel w s, restrWeight p b.1) = (((2 * w) ^ s : ℕ) : ℝ) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, card_pathLabels]
  rw [← Finset.smul_sum, sum_restrWeight_eq_one]
  simp

/-- **The clean unconditional `hnf` switching measure bound.**  For any `ρ`-falsifies-nothing bad set,
`∑_{ρ∈Bad} restrWeight p ρ ≤ (2w · 2p/(1-p))^s`. -/
theorem switching_bound_hnf {w s : ℕ} (p : ℝ) (cs : List (Clause n))
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : (1 - p) / 2 ≠ 0)
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, termFalsified ρ U = false)
    (hactive : ∀ ρ ∈ Bad, (replaySel cs ρ s).card = s)
    (hstars : ∀ ρ ∈ Bad, stars ρ ≤ n) :
    ∑ ρ ∈ Bad, restrWeight p ρ ≤ (p / ((1 - p) / 2)) ^ s * (((2 * w) ^ s : ℕ) : ℝ) := by
  calc ∑ ρ ∈ Bad, restrWeight p ρ
      ≤ (p / ((1 - p) / 2)) ^ s * ∑ b : Restriction n × PathLabel w s, restrWeight p b.1 :=
        switching_measure_bound_hnf p cs hp hp1 hq Bad lab hnf hactive hstars
    _ = (p / ((1 - p) / 2)) ^ s * (((2 * w) ^ s : ℕ) : ℝ) := by rw [sum_prod_fst_restrWeight]

/-!
**Clean `hnf` switching bound proved.**  `∑_{ρ∈Bad} restrWeight p ρ ≤ (2w · 2p/(1-p))^s` for any
`ρ`-falsifies-nothing bad set — the literal switching probability bound, unconditional, fully
assembled and simplified.  The general regime (the confound) remains; not faked.  AC⁰/depth-3;
collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_bound_hnf

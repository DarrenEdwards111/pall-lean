import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPMeasure

/-!
# Håstad switching lemma — total probability `∑ restrWeight = 1` (measure step, last reachable brick)

The headline switching bound `Pr[Bad] ≤ (2w · 2p/(1-p))^s` needs two things from
`switching_measure_bound_modulo_inj`: the injectivity `hinj` (= the confound, the irreducible core)
and the **total-probability identity** `∑_σ restrWeight p σ = 1`.  The latter is *not* the confound —
it is the genuine product-measure fact, and it is reachable.  This brick proves it.

  `restrWeight_eq_prod` — `restrWeight p σ = ∏_i (if σ i = none then p else (1-p)/2)` (the weight is a
    product of independent per-coordinate weights);
  `sum_restrWeight_eq_one` — `∑_σ restrWeight p σ = 1` (sum-of-products = product-of-sums, each
    coordinate summing to `p + (1-p)/2 + (1-p)/2 = 1`).

With this, the RHS of the measure bound is `(2p/(1-p))^s · (2w)^s · 1` — so the entire measure side is
proved; only `hinj` (the confound) remains.

## What is proved (clean axioms, no `sorry`)

* `restrWeight_eq_prod`, `coordWeight_sum`, `sum_restrWeight_eq_one`.

## Honest scope

The total-probability identity — the measure side of the switching lemma, complete.  The remaining
piece is `hinj` (injectivity = the decoder = the confound), genuinely the irreducible core.  Nothing
faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open scoped BigOperators
open Finset

variable {n : ℕ}

/-- **The weight is a product of per-coordinate weights.** -/
theorem restrWeight_eq_prod (p : ℝ) (σ : Restriction n) :
    restrWeight p σ = ∏ i, (if σ i = none then p else (1 - p) / 2) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  unfold restrWeight pweight
  have hfilter : (Finset.univ.filter (fun i => σ i = none)).card = stars σ := rfl
  have htot := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => σ i = none)
  simp only [Finset.card_univ, Fintype.card_fin] at htot
  have hneg : (Finset.univ.filter (fun i => ¬ σ i = none)).card = n - stars σ := by
    rw [hfilter] at htot; omega
  rw [hfilter, hneg]

/-- **The per-coordinate weight sums to `1`.** -/
theorem coordWeight_sum (p : ℝ) :
    ∑ v : Option Bool, (if v = none then p else (1 - p) / 2) = 1 := by
  rw [Fintype.sum_option]; simp; ring

/-- **Total probability: the `p`-biased weight sums to `1`.** -/
theorem sum_restrWeight_eq_one (p : ℝ) : ∑ σ : Restriction n, restrWeight p σ = 1 := by
  have hswap : (∑ σ : Restriction n, ∏ i, (if σ i = none then p else (1 - p) / 2))
      = ∏ _i : Fin n, ∑ v : Option Bool, (if v = none then p else (1 - p) / 2) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  calc ∑ σ : Restriction n, restrWeight p σ
      = ∑ σ : Restriction n, ∏ i, (if σ i = none then p else (1 - p) / 2) := by
        simp_rw [restrWeight_eq_prod]
    _ = ∏ _i : Fin n, ∑ v : Option Bool, (if v = none then p else (1 - p) / 2) := hswap
    _ = ∏ _i : Fin n, (1 : ℝ) := by simp_rw [coordWeight_sum]
    _ = 1 := by simp

/-!
**Total probability proved.**  `∑_σ restrWeight p σ = 1` — the product measure sums to one, completing
the measure side of the switching lemma.  Combined with `switching_measure_bound_modulo_inj` and the
`(2w)^s` code count, the headline `Pr[Bad] ≤ (2w · 2p/(1-p))^s` holds modulo only `hinj` (the
confound).  Nothing faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.sum_restrWeight_eq_one

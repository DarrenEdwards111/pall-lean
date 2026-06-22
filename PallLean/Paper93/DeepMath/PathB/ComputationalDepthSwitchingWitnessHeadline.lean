import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWitnessMeasure
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTotalProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessLabel

/-!
# Håstad switching lemma — the clean unconditional headline `(2wm·2p/(1-p))^s` (PROVED)

The clean finish on `deepest_measure_bound_unconditional`: simplify the right side to the literal
probability bound, via total probability (`sum_restrWeight_eq_one`) and the witness-label count
(`card_witLabels`).  The total weight over `Restriction × WitLabel w s m` is `(2wm)^s`, so the
unconditional probability switching bound reads

  `∑_{ρ∈Bad} restrWeight p ρ ≤ (2wm · 2p/(1-p))^s`   (`deepest_bound_unconditional`),

for any bad set of depth `= s` — **no `hnf`**, general `ρ`.  This is the witness-route analogue of the
`hnf` headline `switching_bound_hnf` (`(2w·2p/(1-p))^s`), unconditional but with the `m=|cs|` factor.

## What is proved (clean axioms, no `sorry`)

* `sum_prod_fst_restrWeight_wit` — `∑_{(σ,c):Restriction×WitLabel} restrWeight p σ = (2wm)^s`.
* `deepest_bound_unconditional` — the clean unconditional probability bound.

## Honest scope

The literal unconditional probability switching bound, `hnf`-free, for general `ρ` — at the non-tight
`(2wm)^s` count (the witness names the live clause; `m=|cs|`).  The tight `(2w)^s` general bound is the
confound proper.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open scoped BigOperators
open SwitchingCounting

variable {n : ℕ}

/-- **The total weight over `Restriction × WitLabel` is `(2wm)^s`.** -/
theorem sum_prod_fst_restrWeight_wit {w s m : ℕ} (p : ℝ) :
    (∑ b : Restriction n × WitLabel w s m, restrWeight p b.1) = (((2 * w * m) ^ s : ℕ) : ℝ) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, card_witLabels]
  rw [← Finset.smul_sum, sum_restrWeight_eq_one]
  simp

/-- **The clean unconditional probability switching bound.**  For any bad set of depth `= s` (clauses
width `≤ w`, count `≤ m`), `∑_{ρ∈Bad} restrWeight p ρ ≤ (2wm · 2p/(1-p))^s` — no `hnf`. -/
theorem deepest_bound_unconditional {w F s m : ℕ} [NeZero w] [NeZero m]
    (p : ℝ) (cs : List (Clause n)) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : (1 - p) / 2 ≠ 0)
    {Bad : Finset (Restriction n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hstars : ∀ ρ ∈ Bad, stars ρ ≤ n) :
    ∑ ρ ∈ Bad, restrWeight p ρ ≤ (p / ((1 - p) / 2)) ^ s * (((2 * w * m) ^ s : ℕ) : ℝ) := by
  calc ∑ ρ ∈ Bad, restrWeight p ρ
      ≤ (p / ((1 - p) / 2)) ^ s * ∑ b : Restriction n × WitLabel w s m, restrWeight p b.1 :=
        deepest_measure_bound_unconditional p cs hp hp1 hq hw hm hdepth hstars
    _ = (p / ((1 - p) / 2)) ^ s * (((2 * w * m) ^ s : ℕ) : ℝ) := by
        rw [sum_prod_fst_restrWeight_wit]

/-!
**Clean unconditional headline proved.**  `∑_{ρ∈Bad} restrWeight p ρ ≤ (2wm · 2p/(1-p))^s` for any
depth-`s` bad set — the literal probability switching bound, `hnf`-free, general `ρ`, via the witness.
Non-tight (`m=|cs|` factor); the tight `(2w)^s` general bound is the confound proper.  AC⁰/depth-3;
collapse + P≠NP untouched.
-/

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_bound_unconditional

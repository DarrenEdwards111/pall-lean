import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFinalWiring
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWitnessInj
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessSeqProps
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarShell

/-!
# Håstad switching lemma — unconditional probability bound via the witness (PROVED)

Wiring `deepest_witness_inj` (the operationally-broken confound: unconditional injectivity) into the
**probability** measure.  The codebase's `deepest_count_witness_unconditional` gives the unconditional
*cardinality* count `|Bad| ≤ |Short|·(2wm)^s`; this is its `restrWeight`-weighted analogue, combining
the witness injection with the measure assembly (`sum_weight_inj_le`) and the deepest star
bookkeeping (`stars_deepestEnd_add_sel`, `deepestSel_card_eq_depth`):

  `∑_{ρ∈Bad} restrWeight p ρ ≤ (2p/(1-p))^s · ∑_{(σ,c) : Restriction × WitLabel w s m} restrWeight p σ`,

**unconditional** (no `hnf`), for any bad set of depth exactly `s`.  The right side is
`(2wm · 2p/(1-p))^s · ∑_σ restrWeight = (2wm · 2p/(1-p))^s` (by `card_witLabels` + total probability).

## What is proved (clean axioms, no `sorry`)

* `restrWeight_deepestEnd` — the deepest weight identity (depth `= s` ⇒ weight scales by `(2p/(1-p))^s`).
* `deepest_measure_bound_unconditional` — the unconditional probability bound.

## Honest scope

The unconditional probability switching bound via the witness — `hnf`-free, general `ρ`.  The cost is
the `m = |cs|` factor in the label (`(2wm)^s`, non-tight): the witness names the live clause rather
than recomputing it.  The tight `(2w)^s` general bound still needs the recomputation decoder (the
confound proper).  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open scoped BigOperators
open SwitchingCounting

variable {n : ℕ}

/-- **The deepest weight identity.**  On the depth-`= s` event, a bad `ρ`'s weight is its end-state
weight scaled by `(2p/(1-p))^s`. -/
theorem restrWeight_deepestEnd (p : ℝ) (cs : List (Clause n)) (F s : ℕ) (ρ : Restriction n)
    (hq : (1 - p) / 2 ≠ 0) (hdepth : (canonicalDT cs F ρ).depth = s) (hn : stars ρ ≤ n) :
    restrWeight p ρ = restrWeight p (deepestEnd cs F ρ) * (p / ((1 - p) / 2)) ^ s := by
  have hstar : stars ρ = stars (deepestEnd cs F ρ) + s := by
    have h1 := stars_deepestEnd_add_sel cs F ρ
    have h2 := deepestSel_card_eq_depth cs F ρ
    rw [h2, hdepth] at h1; omega
  have hjsn : stars (deepestEnd cs F ρ) + s ≤ n := by rw [← hstar]; exact hn
  have hratio := pweight_ratio p n (stars (deepestEnd cs F ρ)) s hjsn
  unfold restrWeight
  rw [hstar, div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero s hq)]
  exact hratio

/-- **Unconditional probability switching bound via the witness.**  For any bad set of depth `= s`
(clauses width `≤ w`, count `≤ m`), the total `p`-biased weight is at most `(2p/(1-p))^s` times the
total weight over `Restriction × WitLabel w s m` — with **no `hnf`**. -/
theorem deepest_measure_bound_unconditional {w F s m : ℕ} [NeZero w] [NeZero m]
    (p : ℝ) (cs : List (Clause n)) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : (1 - p) / 2 ≠ 0)
    {Bad : Finset (Restriction n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hstars : ∀ ρ ∈ Bad, stars ρ ≤ n) :
    ∑ ρ ∈ Bad, restrWeight p ρ
      ≤ (p / ((1 - p) / 2)) ^ s
          * ∑ b : Restriction n × WitLabel w s m, restrWeight p b.1 := by
  refine sum_weight_inj_le Bad
    (fun ρ => (deepestEnd cs F ρ, flatToWitLabel w s m (deepestWitSeq cs F ρ)))
    (fun b => restrWeight p b.1) (restrWeight p) ((p / ((1 - p) / 2)) ^ s) ?_ ?_ ?_ ?_
  · exact pow_nonneg (div_nonneg hp (by linarith)) s
  · exact fun b => restrWeight_nonneg hp hp1 b.1
  · intro x hx y hy hpair
    have hE : deepestEnd cs F x = deepestEnd cs F y := congrArg Prod.fst hpair
    have hWl : flatToWitLabel w s m (deepestWitSeq cs F x)
        = flatToWitLabel w s m (deepestWitSeq cs F y) := congrArg Prod.snd hpair
    have hbnd : ∀ (ρ : Restriction n), ρ ∈ Bad →
        (deepestWitSeq cs F ρ).length = s ∧ ∀ pc ∈ deepestWitSeq cs F ρ, pc.1 < w ∧ pc.2 < m := by
      intro ρ hρ
      refine ⟨(deepestWitSeq_length_eq_depth cs F ρ).trans (hdepth ρ hρ), fun pc hpc => ?_⟩
      exact ⟨(deepestWitSeq_bounds cs hw F ρ pc hpc).1,
        lt_of_lt_of_le (deepestWitSeq_bounds cs hw F ρ pc hpc).2 hm⟩
    have hW : deepestWitSeq cs F x = deepestWitSeq cs F y := by
      rw [← map_finToWit_flatToWitLabel (deepestWitSeq cs F x) (hbnd x hx).1 (hbnd x hx).2,
          ← map_finToWit_flatToWitLabel (deepestWitSeq cs F y) (hbnd y hy).1 (hbnd y hy).2, hWl]
    exact deepest_witness_inj cs F hE hW
  · exact fun ρ hρ =>
      (restrWeight_deepestEnd p cs F s ρ hq (hdepth ρ hρ) (hstars ρ hρ)).trans (mul_comm _ _)

/-!
**Unconditional probability bound via the witness, proved.**  `∑_{Bad} restrWeight ≤ (2p/(1-p))^s ·
(witness total)`, `hnf`-free, general `ρ` — the measure-weighted analogue of
`deepest_count_witness_unconditional`, powered by `deepest_witness_inj` (the operationally-broken
confound).  Cost: the `m=|cs|` label factor (non-tight); the tight `(2w)^s` general bound still needs
the recomputation decoder (the confound proper).  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_measure_bound_unconditional

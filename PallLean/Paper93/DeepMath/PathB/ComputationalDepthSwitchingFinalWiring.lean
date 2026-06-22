import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingMeasureAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel

/-!
# Håstad switching lemma — final wiring of the measure step (and an honest finding)

Assembling all the measure-step bricks (`sum_weight_inj_le`, `restrWeight_replayPath`,
`stars_replayPath`, `pweight_ratio`) into the switching bound:

  `∑_{ρ∈Bad} restrWeight p ρ ≤ (2p/(1-p))^s · ∑_{(σ,c)} restrWeight p σ`   (`switching_measure_bound_modulo_inj`),

where the right side `= (2w)^s · (2p/(1-p))^s · ∑_σ restrWeight p σ` (sum over `Restriction × PathLabel`,
the `(2w)^s` codes), and `∑_σ restrWeight p σ = 1` (total probability) finishes the headline
`Pr[Bad] ≤ (2w · 2p/(1-p))^s ≈ (5pw)^s`.

## Honest finding — the confound reappears as injectivity

The wiring needs `hinj`: the map `ρ ↦ (replayPath cs ρ s, lab ρ)` is **injective** on `Bad`.  For a
finite map, injectivity is *equivalent* to decodability — recovering `ρ` from `(end-state, label)`.
That is exactly the decoder, hence **exactly the confound**.  So the probabilistic route does *not*
sidestep the confound after all: the measure assembly (the *weighting*) is genuine and proved, but it
multiplies an injectivity that is the same recover-`ρ`-from-end-state problem the deterministic routes
hit.  The classical proof obtains `hinj` from Razborov's satisfy-encoding decoder; the codebase
obtains it only for the `ρ`-falsifies-nothing regime (`recoverStream_correct`).  So `hinj` is left as
an explicit hypothesis here — **not** faked.

This is the honest culmination: every route (deterministic decoder ×3, probabilistic measure) reduces
the switching lemma to the *same* primitive — recover `ρ` from `(end-state, label)`, i.e. the confound
— with everything *else* (the measure weighting, the counts, the structure) now proved.

## What is proved (clean axioms, no `sorry`)

* `restrWeight_nonneg` — `0 ≤ restrWeight p ρ` for `0 ≤ p ≤ 1`.
* `switching_measure_bound_modulo_inj` — the switching measure bound, modulo the injectivity `hinj`.

## Honest scope

The complete measure assembly, modulo the injectivity (= the confound) and the total-probability
identity `∑ restrWeight = 1`.  Nothing faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP
untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open scoped BigOperators
open Depth3

variable {n : ℕ}

/-- The `p`-biased weight is nonnegative for `0 ≤ p ≤ 1`. -/
theorem restrWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ρ : Restriction n) :
    0 ≤ restrWeight p ρ := by
  unfold restrWeight pweight
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (by linarith) _)

/-- **Switching measure bound, modulo injectivity.**  The total `p`-biased weight of the bad set is
at most `(2p/(1-p))^s` times the total weight over `Restriction × PathLabel` — given the injection
`ρ ↦ (end-state, label)` is injective on `Bad` (the confound), all `s` steps are active, and stars are
bounded by `n`. -/
theorem switching_measure_bound_modulo_inj {w s : ℕ} (p : ℝ) (cs : List (Clause n))
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : (1 - p) / 2 ≠ 0)
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (hactive : ∀ ρ ∈ Bad, (replaySel cs ρ s).card = s)
    (hstars : ∀ ρ ∈ Bad, stars ρ ≤ n)
    (hinj : ∀ x ∈ Bad, ∀ y ∈ Bad,
      (replayPath cs x s, lab x) = (replayPath cs y s, lab y) → x = y) :
    ∑ ρ ∈ Bad, restrWeight p ρ
      ≤ (p / ((1 - p) / 2)) ^ s * ∑ b : Restriction n × PathLabel w s, restrWeight p b.1 := by
  refine sum_weight_inj_le Bad (fun ρ => (replayPath cs ρ s, lab ρ))
    (fun b => restrWeight p b.1) (restrWeight p) ((p / ((1 - p) / 2)) ^ s) ?_ ?_ hinj ?_
  · exact pow_nonneg (div_nonneg hp (by linarith)) s
  · exact fun b => restrWeight_nonneg hp hp1 b.1
  · exact fun ρ hρ =>
      (restrWeight_replayPath p cs ρ s hq (hactive ρ hρ) (hstars ρ hρ)).trans (mul_comm _ _)

/-!
**Measure step fully wired, modulo injectivity.**  All the measure-step bricks combine into the
switching bound `∑_{Bad} restrWeight ≤ (2p/(1-p))^s · ∑(weights over codes)`.  The sole remaining
hypothesis is `hinj` — the injectivity of `ρ ↦ (end-state, label)`, equivalently the decoder,
equivalently the confound.  Every route (3 deterministic decoders + this probabilistic measure)
reduces the switching lemma to that same primitive, with everything else proved.  `hinj` is left
explicit — **not** faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_measure_bound_modulo_inj

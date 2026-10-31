import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting

/-!
# Håstad switching lemma — probabilistic measure step, foundation (first brick)

The classical switching lemma is **probabilistic**: under the `p`-biased random restriction (each
variable independently free w.p. `p`, fixed to `0`/`1` each w.p. `(1-p)/2`), `Pr[bad] ≤ (5pw)^s`.
The counting injection `Bad ↪ ShortRestrictions × StarPatterns` (the decoder work) bounds *cardinality*;
the measure step weights it.  The arithmetic core is the **weight ratio**: a restriction's
probability is `p^{stars} · ((1-p)/2)^{n-stars}`, so fixing `s` more variables multiplies the weight
by `(p / ((1-p)/2))^s = (2p/(1-p))^s`.

This brick lays the foundation: the `p`-biased weight and its `s`-fold ratio.

  `restrWeight p ρ = pweight p n (stars ρ)`,
  `pweight_ratio : pweight p n (j+s) · ((1-p)/2)^s = pweight p n j · p^s`   (the cross-multiplied ratio).

So a bad `ρ` (with `stars ρ = j+s` free vars) and its short image `ρ'` (`stars ρ' = j`) satisfy
`weight ρ · ((1-p)/2)^s = weight ρ' · p^s`, i.e. `weight ρ = weight ρ' · (2p/(1-p))^s` — the per-`ρ`
weight transfer the measure bound sums over.

## Plan (see `PROBABILISTIC_MEASURE_SCOPE.md`)

1. **weight ratio** (this brick) — `pweight_ratio`.
2. **injection** — `ρ ↦ (replayPath cs ρ s, lab ρ)` is injective on the bad set (already:
   `replayPath_inj` + the decoder); each bad `ρ` has `stars = stars(ρ') + s`.
3. **measure assembly** — `Pr[Bad] = ∑_{ρ∈Bad} weight ρ = (2p/(1-p))^s ∑ weight ρ' ≤ (2w)^s · (2p/(1-p))^s`
   via the injection (each code's `ρ'`-fiber sums to `≤ 1`) — the new probabilistic step.

## What is proved (clean axioms, no `sorry`)

* `pweight` / `restrWeight` — the `p`-biased weight (by stars) of a restriction.
* `pweight_ratio` — the `s`-fold weight ratio (cross-multiplied form).

## Honest scope

The weight-ratio arithmetic foundation of the measure step.  The injection and the measure assembly
(summing over the bad set) are the remaining probabilistic bricks; not faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {n : ℕ}

/-- The `p`-biased probability weight of a restriction with `k` free variables (`stars`) among `n`:
`p^k · ((1-p)/2)^{n-k}`. -/
noncomputable def pweight (p : ℝ) (n k : ℕ) : ℝ := p ^ k * ((1 - p) / 2) ^ (n - k)

/-- The `p`-biased weight of a restriction `ρ` (depends only on its star count). -/
noncomputable def restrWeight (p : ℝ) (ρ : Restriction n) : ℝ := pweight p n (stars ρ)

/-- **The `s`-fold weight ratio (cross-multiplied).**  A restriction with `j+s` free variables and
one with `j` free variables satisfy `weight(j+s) · ((1-p)/2)^s = weight(j) · p^s`. -/
theorem pweight_ratio (p : ℝ) (n j s : ℕ) (h : j + s ≤ n) :
    pweight p n (j + s) * ((1 - p) / 2) ^ s = pweight p n j * p ^ s := by
  unfold pweight
  have hp : (p : ℝ) ^ (j + s) = p ^ j * p ^ s := pow_add p j s
  have hq : ((1 - p) / 2 : ℝ) ^ (n - j)
      = ((1 - p) / 2) ^ (n - (j + s)) * ((1 - p) / 2) ^ s := by
    rw [← pow_add]; congr 1; omega
  rw [hp, hq]; ring

/-!
**Weight-ratio foundation proved.**  The `p`-biased weight is `pweight p n (stars ρ)`, and fixing `s`
more variables transfers the weight by the factor `(2p/(1-p))^s` (`pweight_ratio`, cross-multiplied).
This is the arithmetic core of the measure bound `Pr[Bad] ≤ (2w)^s · (2p/(1-p))^s`.  The injection and
the measure assembly are the remaining probabilistic bricks; not faked.  AC⁰/depth-3; collapse + P≠NP
untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.pweight_ratio

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPMeasure
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStarsPath

/-!
# Håstad switching lemma — the measure assembly (probabilistic core)

The genuine probabilistic step.  Two components:

1. **Weighted-injection bound** (`sum_weight_inj_le`) — the assembly mechanism.  If a weight `w` on a
   bad set factors as `w a = c · v (f a)` through an injection `f` into a fintype, then
   `∑_{a∈Bad} w a ≤ c · ∑_b v b`.  This is the abstract heart of the measure bound.

2. **Per-`ρ` weight identity** (`restrWeight_replayPath`) — combining the star bookkeeping
   (`stars_replayPath`) with the weight ratio (`pweight_ratio`): a bad `ρ` (all `s` steps active) has
   `restrWeight p ρ = restrWeight p (replayPath cs ρ s) · (2p/(1-p))^s`.

Together: instantiating `sum_weight_inj_le` with `f = ρ ↦ (end-state, label)` (injective via
`replayPath_inj` + the decoder), `c = (2p/(1-p))^s`, and `v` the short-state weight, bounds
`Pr[Bad] = ∑_{ρ∈Bad} restrWeight p ρ` by `(2p/(1-p))^s · ∑ (short weights)` — and `∑ short weights ≤
(2w)^s · 1` finishes the switching bound.  This is the route **around** the confound: it uses the
injection as an *injection*, never as a from-end-state decoder.

## What is proved (clean axioms, no `sorry`)

* `sum_weight_inj_le` — the weighted-injection bound (assembly mechanism).
* `restrWeight_replayPath` — the per-`ρ` weight identity (star bookkeeping × weight ratio).

## Honest scope

The two genuine components of the measure assembly.  The final headline needs the concrete injection
(`replayPath_inj` + label, present) and the total short-weight bound (`∑ ≤ (2w)^s`); wiring those is
the remaining step.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open scoped BigOperators
open Depth3

variable {n : ℕ}

/-- **Weighted-injection bound (assembly mechanism).**  A weight factoring as `w a = c · v (f a)`
through an injection `f` into a fintype, with `c ≥ 0` and `v ≥ 0`, sums over `Bad` to `≤ c · ∑ v`. -/
theorem sum_weight_inj_le {α β : Type*} [Fintype β] [DecidableEq β]
    (Bad : Finset α) (f : α → β) (v : β → ℝ) (w : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hv : ∀ b, 0 ≤ v b)
    (hinj : ∀ x ∈ Bad, ∀ y ∈ Bad, f x = f y → x = y)
    (hw : ∀ a ∈ Bad, w a = c * v (f a)) :
    ∑ a ∈ Bad, w a ≤ c * ∑ b, v b := by
  calc ∑ a ∈ Bad, w a = ∑ a ∈ Bad, c * v (f a) := Finset.sum_congr rfl hw
    _ = c * ∑ a ∈ Bad, v (f a) := by rw [Finset.mul_sum]
    _ = c * ∑ b ∈ Bad.image f, v b := by rw [← Finset.sum_image hinj]
    _ ≤ c * ∑ b, v b := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hv b)

/-- **Per-`ρ` weight identity.**  When the path selects exactly `s` coordinates (all `s` steps
active), the bad `ρ`'s weight is its end-state weight scaled by `(2p/(1-p))^s = (p/((1-p)/2))^s`. -/
theorem restrWeight_replayPath (p : ℝ) (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ)
    (hq : (1 - p) / 2 ≠ 0) (hcard : (replaySel cs ρ s).card = s) (hn : stars ρ ≤ n) :
    restrWeight p ρ = restrWeight p (replayPath cs ρ s) * (p / ((1 - p) / 2)) ^ s := by
  have hstar : stars ρ = stars (replayPath cs ρ s) + s := by
    have h := stars_replayPath cs ρ s; omega
  have hjsn : stars (replayPath cs ρ s) + s ≤ n := by rw [← hstar]; exact hn
  have hratio := pweight_ratio p n (stars (replayPath cs ρ s)) s hjsn
  unfold restrWeight
  rw [hstar, div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero s hq)]
  exact hratio

/-!
**Measure-assembly core proved.**  The weighted-injection bound and the per-`ρ` weight identity — the
two genuine components of `Pr[Bad] ≤ (2p/(1-p))^s · ∑ (short weights)`.  Instantiating with the
concrete injection (`replayPath_inj` + label) and the total short-weight bound `≤ (2w)^s` gives the
switching bound; that final wiring is the remaining step.  The injection is used as an *injection*
(not a decoder), so the confound does not block this route.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.sum_weight_inj_le
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.restrWeight_replayPath

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFinalWiring
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder

/-!
# Håstad switching lemma — unconditional measure bound for the `hnf` regime (live-DNF reindexing, first brick)

Route 1 (live-DNF reindexing): discharge `hinj` where it is genuinely provable — the
**ρ-falsifies-nothing (`hnf`)** regime — using the existing `hnf` decoder.

The injectivity `ρ ↦ (replayPath cs ρ s, lab ρ)` is, for `hnf`-restrictions, dischargeable **without
the label**: `decodedSel_eq_replaySel` recovers `replaySel cs ρ s` from the end-state alone, and
`replayPath_inj` then recovers `ρ`.  So `switching_measure_bound_modulo_inj` becomes **unconditional**
on any `hnf`-bad-set:

  `∑_{ρ∈Bad} restrWeight p ρ ≤ (2p/(1-p))^s · ∑_{(σ,c)} restrWeight p σ`   (`switching_measure_bound_hnf`),

with no `hinj` hypothesis.  This is the first **unconditional** switching measure bound in the arc
(everything earlier was modulo `hinj`).  It is the `hnf` case — the live sub-DNF case — exactly where
the confound is absent.

## What is proved (clean axioms, no `sorry`)

* `switching_measure_bound_hnf` — the measure bound, unconditional, for any `hnf`-bad-set.

## Honest scope

The switching measure bound, fully unconditional, for the `ρ`-falsifies-nothing regime — `hinj`
discharged via the `hnf` decoder (`decodedSel_eq_replaySel` + `replayPath_inj`).  The general regime
(ρ may falsify terms) still needs identifying the live sub-DNF from the leaf (the confound); reindexing
the *general* bad event onto live sub-DNFs is the remaining step.  Nothing faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.  See `SATISFY_DECODER_SCOPE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open scoped BigOperators
open Depth3

variable {n : ℕ}

/-- **Unconditional switching measure bound for the `hnf` regime.**  On any bad set of restrictions
that each falsify no term, the measure bound holds with no injectivity hypothesis — `hinj` is
discharged via the `hnf` end-state decoder. -/
theorem switching_measure_bound_hnf {w s : ℕ} (p : ℝ) (cs : List (Clause n))
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : (1 - p) / 2 ≠ 0)
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, termFalsified ρ U = false)
    (hactive : ∀ ρ ∈ Bad, (replaySel cs ρ s).card = s)
    (hstars : ∀ ρ ∈ Bad, stars ρ ≤ n) :
    ∑ ρ ∈ Bad, restrWeight p ρ
      ≤ (p / ((1 - p) / 2)) ^ s * ∑ b : Restriction n × PathLabel w s, restrWeight p b.1 := by
  refine switching_measure_bound_modulo_inj p cs hp hp1 hq Bad lab hactive hstars ?_
  intro x hx y hy hpair
  have hpx : replayPath cs x s = replayPath cs y s := congrArg Prod.fst hpair
  have hsel : replaySel cs x s = replaySel cs y s := by
    rw [← decodedSel_eq_replaySel (hnf x hx) s, ← decodedSel_eq_replaySel (hnf y hy) s, hpx]
  exact replayPath_inj cs s hpx hsel

/-!
**Unconditional `hnf` switching bound proved.**  `hinj` is discharged on the `ρ`-falsifies-nothing
regime via `decodedSel_eq_replaySel` (recover `replaySel` from the leaf) + `replayPath_inj` (recover
`ρ`) — no label needed.  This is the live sub-DNF case (confound absent), the first unconditional
switching measure bound here.  The general regime still needs reindexing the bad event onto live
sub-DNFs; not faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_measure_bound_hnf

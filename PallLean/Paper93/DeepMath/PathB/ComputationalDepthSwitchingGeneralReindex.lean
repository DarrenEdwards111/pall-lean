import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHnfHeadline
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingLiveDNFPath

/-!
# Håstad switching lemma — general-regime reindexing (the live-DNF partition bound)

The general regime (`ρ` may falsify terms), reindexed onto live sub-DNFs.  The bad set partitions by
`liveCs ρ cs` (which terms `ρ` does *not* falsify); on each fiber, `ρ` falsifies nothing in its live
sub-DNF, so the **unconditional `hnf` bound** (`switching_bound_hnf`) applies — with the descent on
`cs` and on `liveCs ρ cs` coinciding (`replaySel_liveCs`).  Summing over the fibers gives

  `∑_{ρ∈Bad} restrWeight p ρ ≤ (#distinct live sub-DNFs) · (2w · 2p/(1-p))^s`   (`switching_bound_general`).

## Honest reading — this is the *weak* bound; the factor is the confound's cost

The extra factor `#distinct live sub-DNFs` (`≤ 2^{|cs|}`) is precisely the price of **not** breaking
the confound.  The tight Håstad bound `(5pw)^s` avoids it by having the decoder identify the live
sub-DNF from the leaf+code — which is exactly the confound, and is *not* available deterministically.
This reindexing trades the confound for the subset-enumeration factor: faithful, genuine, and `hnf`-
free, but **weaker than Håstad** and not usable for the depth-3 lower bound (which needs the tight
`(5pw)^s`).  So this is the honest extent of the general regime *without* the confound; the tight
general bound remains the confound.

## What is proved (clean axioms, no `sorry`)

* `switching_bound_general` — the live-DNF partition bound for general `ρ`.

## Honest scope

The faithful general-regime reindexing — the weak `(#live-sub-DNFs)·(5pw)^s` bound.  The tight general
bound is the confound, **not** faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open scoped BigOperators
open Depth3

variable {n : ℕ}

open Classical in
/-- **General-regime reindexing (weak bound).**  The bad weight is at most the number of distinct
live sub-DNFs times the `hnf` switching bound — the confound's cost made explicit. -/
theorem switching_bound_general {w s : ℕ} (p : ℝ) (cs : List (Clause n))
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : (1 - p) / 2 ≠ 0)
    (Bad : Finset (Restriction n)) (lab : Restriction n → PathLabel w s)
    (hactive : ∀ ρ ∈ Bad, (replaySel cs ρ s).card = s)
    (hstars : ∀ ρ ∈ Bad, stars ρ ≤ n) :
    ∑ ρ ∈ Bad, restrWeight p ρ
      ≤ (Bad.image (fun ρ => liveCs ρ cs)).card
          • ((p / ((1 - p) / 2)) ^ s * (((2 * w) ^ s : ℕ) : ℝ)) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ρ => liveCs ρ cs)
    (fun ρ hρ => Finset.mem_image_of_mem _ hρ)]
  refine Finset.sum_le_card_nsmul _ _ _ (fun L hL => ?_)
  refine switching_bound_hnf p L hp hp1 hq
    (Bad.filter (fun ρ => liveCs ρ cs = L)) lab ?_ ?_ ?_
  · intro ρ hρ U hU
    rw [Finset.mem_filter] at hρ
    rw [← hρ.2] at hU
    exact liveCs_hnf ρ cs U hU
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    rw [← hρ.2, replaySel_liveCs]
    exact hactive ρ hρ.1
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    exact hstars ρ hρ.1

/-!
**General-regime reindexing proved (weak bound).**  `∑_{Bad} restrWeight ≤ (#live-sub-DNFs)·(5pw)^s`
— the faithful general bound obtainable without the confound, with the `#live-sub-DNFs` factor (`≤
2^{|cs|}`) being exactly the confound's cost.  The tight `(5pw)^s` general bound remains the confound;
not faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_bound_general

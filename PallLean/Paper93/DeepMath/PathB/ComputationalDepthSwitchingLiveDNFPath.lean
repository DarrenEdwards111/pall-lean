import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingLiveDNF
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath

/-!
# Håstad switching lemma — live-DNF normalization lifted through the replay path (second brick)

`activeTerm_liveCs` showed the active term is unchanged by dropping `ρ`-falsified terms (given they
stay falsified at the current state).  Along the replay path this hypothesis is automatic
(`termFalsified_replayPath_of`: a `ρ`-falsified term stays falsified at every `replayPath cs ρ k`).
This brick lifts the invariance through the whole process:

  `replayPath (liveCs ρ cs) ρ k = replayPath cs ρ k`   (`replayPath_liveCs`),
  `replaySel  (liveCs ρ cs) ρ k = replaySel  cs ρ k`   (`replaySel_liveCs`).

So a general `ρ` and its live sub-DNF produce **identical** replay paths and selected sets — and `ρ`
falsifies nothing in the live sub-DNF (`liveCs_hnf`).  This is the reduction of the general case to
the proved `ρ`-falsifies-nothing case, at the path/selected-set level.

## What is proved (clean axioms, no `sorry`)

* `activeTermLit_liveCs` / `replayStep_liveCs` — the per-step invariance lifts to the literal and step.
* `replayPath_liveCs` / `replaySel_liveCs` — **the full path and selected set are unchanged** by
  live-DNF restriction.

## Honest scope

The replay path and selected set are invariant under live-DNF restriction.  Combining this with the
`hnf` decoder (`decodedSel_eq_replaySel` / `replay_count_nothing_falsified_setroute`) to obtain the
general-case count is the remaining assembly (next brick); the probabilistic switching lemma is
separate.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The active literal is unchanged by live-DNF restriction (given the monotonicity hypothesis). -/
theorem activeTermLit_liveCs {ρ : Restriction n} {cs : List (Clause n)} {σ : Restriction n}
    (hmono : ∀ T ∈ cs, termFalsified ρ T = true → termFalsified σ T = true) :
    activeTermLit (liveCs ρ cs) σ = activeTermLit cs σ := by
  unfold activeTermLit
  rw [activeTerm_liveCs hmono]

/-- The replay step is unchanged by live-DNF restriction (given the monotonicity hypothesis). -/
theorem replayStep_liveCs {ρ : Restriction n} {cs : List (Clause n)} {σ : Restriction n}
    (hmono : ∀ T ∈ cs, termFalsified ρ T = true → termFalsified σ T = true) :
    replayStep (liveCs ρ cs) σ = replayStep cs σ := by
  unfold replayStep
  rw [activeTermLit_liveCs hmono]

/-- **The replay path is unchanged by live-DNF restriction.** -/
theorem replayPath_liveCs (ρ : Restriction n) (cs : List (Clause n)) (k : ℕ) :
    replayPath (liveCs ρ cs) ρ k = replayPath cs ρ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show replayStep (liveCs ρ cs) (replayPath (liveCs ρ cs) ρ k)
        = replayStep cs (replayPath cs ρ k)
    rw [ih, replayStep_liveCs (fun T _ hf => termFalsified_replayPath_of k hf)]

/-- **The selected set is unchanged by live-DNF restriction.** -/
theorem replaySel_liveCs (ρ : Restriction n) (cs : List (Clause n)) (k : ℕ) :
    replaySel (liveCs ρ cs) ρ k = replaySel cs ρ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [replaySel, replaySel, ih, replayPath_liveCs,
      activeTermLit_liveCs (fun T _ hf => termFalsified_replayPath_of k hf)]

/-!
**Replay path and selected set invariant under live-DNF restriction, proved.**  A general `ρ` and its
live sub-DNF produce identical replay paths and selected sets, and `ρ` falsifies nothing in the live
sub-DNF — the reduction of the general case to the proved `hnf` case at the path level.  Combining
with the `hnf` decoder for the general-case count is the remaining assembly; not faked.  AC⁰/depth-3;
collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replayPath_liveCs
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replaySel_liveCs

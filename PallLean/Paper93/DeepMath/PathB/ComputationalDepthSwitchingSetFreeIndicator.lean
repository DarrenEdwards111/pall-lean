import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSetCountModulo

/-!
# Håstad switching lemma — constructing `isFree` (set-based route, fourth brick)

Taking a run at the remaining primitive: construct the ρ-free indicator `isFree` of
`replay_count_modulo_freeIndicator`.

**What works (the no-confound regime).**  When `ρ` falsifies nothing, `decodedSel` has *no* ρ-fixed
excess (`decodedSel = replaySel`, every read-off variable is path-fixed), so the **trivial**
indicator `isFree ≡ true` already satisfies the oracle hypothesis.  This discharges the full
`(2w)^s` count via the set-route framework, recovering `replay_count_nothing_falsified`
(`replay_count_nothing_falsified_setroute`).  So the entire set-based chain (completeness →
decomposition → count-modulo → indicator) closes end-to-end, unconditionally, in this regime.

**Where it bites (the confound).**  In the general case (ρ may falsify terms) the trivial indicator
fails: `decodedSel` contains ρ-fixed variables that are *not* ρ-free, so `isFree` must return `false`
on them.  Distinguishing a path-fixed false-literal variable from a ρ-fixed one at the end-state
requires identifying the path (equivalently the per-step active terms) — which the `(2w)^s` label
records only as *positions within active terms*, not as variables.  Recovering the terms from the
end-state is exactly the confound (`confound_uncovered`); the label-positions alone are insufficient.
A non-trivial `isFree` for the general case is therefore **not** constructed here and is **not**
faked.

## What is proved (clean axioms, no `sorry`)

* `replay_count_nothing_falsified_setroute` — the `(2w)^s` count for the ρ-falsifies-nothing regime,
  via the set-route framework with the trivial indicator `isFree ≡ true`.

## Honest scope

`isFree` is constructed (trivially) exactly where there is no ρ-fixed excess (no confound).  The
general-case `isFree` is the confound and is **not** faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **The set-route count for the ρ-falsifies-nothing regime, via the trivial ρ-free indicator.**
With no ρ-fixed excess, `isFree ≡ true` recovers `replaySel = decodedSel`, closing the `(2w)^s`
count through the set-route framework. -/
theorem replay_count_nothing_falsified_setroute {w s : ℕ} {cs : List (Clause n)}
    (lab : Restriction n → PathLabel w s)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, replayPath cs ρ s ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, termFalsified ρ T = false) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine replay_count_modulo_freeIndicator lab (fun _ _ _ => true) hmem ?_
  intro ρ hρ v hv
  rw [decodedSel_eq_replaySel (hnf ρ hρ) s] at hv
  exact ⟨fun _ => mem_freeVars.mp (replaySel_subset_freeVars cs ρ s hv), fun _ => rfl⟩

/-!
**`isFree` constructed where the confound is absent.**  The trivial indicator closes the set-route
`(2w)^s` count for the ρ-falsifies-nothing regime — the whole set chain runs end-to-end there.  The
general-case `isFree` (distinguishing path-fixed from ρ-fixed false-literal variables at the
end-state) requires recovering the per-step active terms from the end-state, which the
label-positions alone cannot supply — the confound, **not** faked.  AC⁰/depth-3; collapse + P≠NP
untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_count_nothing_falsified_setroute

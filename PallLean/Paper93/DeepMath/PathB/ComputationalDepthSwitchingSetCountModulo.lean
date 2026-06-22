import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSetDecoderDecomp

/-!
# Håstad switching lemma — set-route count modulo a ρ-free indicator (set-based route, third brick)

The set-based analogue of the count reduction, and the cleanest isolation of the confound.  By the
exact decomposition `replaySel = decodedSel ∩ {ρ-free}`, the decoder needs only one extra bit of
information beyond the (end-state-computable) `decodedSel`: **which of `decodedSel`'s variables are
ρ-free**.  This brick discharges the full `(2w)^s` count given precisely that, via the set decoder
`D π label = decodedSel.filter (isFree π label)`:

  `Bad.card ≤ Short.card · (2w)^s`,  given  `isFree (end-state) (label) v ↔ ρ v = none`  on `decodedSel`.

So the entire general-case obstruction is reduced to **one Boolean primitive** — recover, from the
end-state and the `(2w)^s` label, the ρ-free indicator on `decodedSel`.  This is lighter than the
per-step `recT` of the earlier route (a single Boolean per variable, not a clause per step), and it
is the genuine remaining core (the confound).  It is **not** discharged or faked here.

## What is proved (clean axioms, no `sorry`)

* `replay_count_modulo_freeIndicator` — **the `(2w)^s` count modulo the ρ-free indicator oracle**,
  with the set decoder `decodedSel.filter isFree`.

## Honest scope

Reduces the general-case switching count to the single Boolean primitive "recover the ρ-free
indicator on `decodedSel` from the end-state + label."  That primitive is the confound and is **not**
faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **The `(2w)^s` count modulo a ρ-free indicator.**  If `isFree`, computed from the end-state and
the label, recovers the ρ-free indicator on `decodedSel`, then the set decoder
`decodedSel.filter isFree` recovers `replaySel` and the switching count holds. -/
theorem replay_count_modulo_freeIndicator {w s : ℕ} {cs : List (Clause n)}
    (lab : Restriction n → PathLabel w s)
    (isFree : Restriction n → PathLabel w s → Fin n → Bool)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, replayPath cs ρ s ∈ Short)
    (hfree : ∀ ρ ∈ Bad, ∀ v ∈ decodedSel cs (replayPath cs ρ s),
      (isFree (replayPath cs ρ s) (lab ρ) v = true ↔ ρ v = none)) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  classical
  refine replay_switching_count lab
    (fun π label => (decodedSel cs π).filter (fun v => isFree π label v = true)) hmem ?_
  intro ρ hρ
  show (decodedSel cs (replayPath cs ρ s)).filter
      (fun v => isFree (replayPath cs ρ s) (lab ρ) v = true) = replaySel cs ρ s
  rw [replaySel_eq_decodedSel_filter]
  exact Finset.filter_congr (fun v hv => hfree ρ hρ v hv)

/-!
**Set-route count modulo the ρ-free indicator, proved.**  The general-case switching count reduces
to the single Boolean primitive "recover the ρ-free indicator on `decodedSel` from the end-state and
the `(2w)^s` label" — the set decoder `decodedSel.filter isFree` does the rest.  That primitive is the
confound and is **not** faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_count_modulo_freeIndicator

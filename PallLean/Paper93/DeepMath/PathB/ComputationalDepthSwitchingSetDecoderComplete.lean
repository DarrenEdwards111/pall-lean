import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTermLabelInverse

/-!
# Håstad switching lemma — set-decoder completeness is unconditional (set-based route, first brick)

Switching to the **set-based decoder** route (the correct line past the per-step `recT` confound).
`EndStateDecoder.decodedSel cs π` reads off the variables carrying a false literal of a falsified
term at the end-state `π`.  `decodedSel_eq_replaySel` proves `decodedSel = replaySel` for the
**ρ-falsifies-nothing** regime; the general case (ρ may itself falsify terms) is open because
`decodedSel` then **over-counts** ρ-fixed false-literal variables.

This brick isolates the easy half precisely: **completeness holds unconditionally**.  Every
path-selected variable carries a false literal of a falsified term at the end-state — regardless of
whether ρ falsifies anything — so

  `replaySel cs ρ s ⊆ decodedSel cs (replayPath cs ρ s)`   (`replaySel_subset_decodedSel`).

So the *only* gap in the general case is the reverse inclusion: trimming the ρ-fixed false-literal
variables that `decodedSel` spuriously includes.  That trimming (the genuine general-case work, where
the label earns its keep) is **not** done here and is **not** faked.

## What is proved (clean axioms, no `sorry`)

* `replaySel_subset_decodedSel` — **unconditional completeness** of the set decoder.

## Honest scope

Completeness of the set decoder, with no regime hypothesis.  The reverse inclusion for general ρ
(soundness / trimming the spurious ρ-fixed variables) is the open general-case core and is **not**
faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Set-decoder completeness, unconditional.**  Every path-selected variable carries a false
literal of a falsified term at the end-state — no `ρ`-falsifies-nothing hypothesis needed. -/
theorem replaySel_subset_decodedSel (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    replaySel cs ρ s ⊆ decodedSel cs (replayPath cs ρ s) := by
  intro v hv
  obtain ⟨k, hk, ℓ, hℓ, hℓv⟩ := mem_replaySel s hv
  obtain ⟨T, hTactive⟩ : ∃ T, activeTerm cs (replayPath cs ρ k) = some T := by
    unfold activeTermLit at hℓ
    cases hat : activeTerm cs (replayPath cs ρ k) with
    | none => rw [hat] at hℓ; simp at hℓ
    | some T => exact ⟨T, rfl⟩
  have hℓT : ℓ ∈ T.lits := activeTermLit_mem_term hTactive hℓ
  have hℓfalse : litFalse (replayPath cs ρ s) ℓ = true := by
    have h1 : litFalse (replayPath cs ρ (k + 1)) ℓ = true := by
      rw [replayPath, replayStep, hℓ]; simp [litFalse, falFix_forces_false]
    have h2 := litFalse_replayPath_of (cs := cs) (σ := replayPath cs ρ (k + 1)) (s - (k + 1)) h1
    rwa [replayPath_add, show (k + 1) + (s - (k + 1)) = s from by omega] at h2
  have hTf : termFalsified (replayPath cs ρ s) T = true :=
    termFalsified_of_active_lit_mem hk hℓ hℓT
  rw [decodedSel, Finset.mem_filter]
  exact ⟨Finset.mem_univ v, T, activeTerm_mem hTactive, hTf, ℓ, hℓT, hℓv, hℓfalse⟩

/-!
**Set-decoder completeness, proved unconditionally.**  `replaySel ⊆ decodedSel` with no regime
hypothesis — the easy half of the set-based decoder for general ρ.  The reverse inclusion (trimming
the spurious ρ-fixed false-literal variables, where the label is needed) is the open general-case
core and is **not** faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replaySel_subset_decodedSel

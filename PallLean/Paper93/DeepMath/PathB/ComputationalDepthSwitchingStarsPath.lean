import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReadOnceId
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFixStable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPolarity

/-!
# Håstad switching lemma — star bookkeeping for the measure step (second brick)

The injection `ρ ↦ (replayPath cs ρ s, lab ρ)` of the measure step needs the star (free-variable)
relation between a restriction and its end-state: **the replay path fixes exactly the selected
coordinates**, so the end-state has `stars ρ − |replaySel|` free variables.  This brick proves it.

  `replaySel_isSome` — a selected variable is fixed at the end-state;
  `freeVars_replayPath_eq` — `freeVars (replayPath cs ρ s) = freeVars ρ \ replaySel cs ρ s`;
  `stars_replayPath` — `stars (replayPath cs ρ s) + (replaySel cs ρ s).card = stars ρ`.

With `(replaySel cs ρ s).card = s` (when all `s` steps are active), this gives
`stars ρ = stars (end-state) + s`, the exact star drop the weight ratio (`pweight_ratio`) consumes.

## What is proved (clean axioms, no `sorry`)

* `replaySel_isSome`, `freeVars_replayPath_eq`, `stars_replayPath`.

## Honest scope

The star bookkeeping feeding the measure step's weight ratio.  The measure assembly (summing the
weighted injection over the bad set) is the remaining probabilistic brick; not faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.  See `PROBABILISTIC_MEASURE_SCOPE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **A selected variable is fixed at the end-state.**  Once the path selects `v` (at some step
`k < s`), `replayStep` fixes it and the fixing persists to the end. -/
theorem replaySel_isSome {cs : List (Clause n)} {ρ : Restriction n} {s : ℕ} {v : Fin n}
    (hv : v ∈ replaySel cs ρ s) : replayPath cs ρ s v ≠ none := by
  obtain ⟨k, hk, ℓ, hℓ, hℓv⟩ := mem_replaySel s hv
  have hk1 : replayPath cs ρ (k + 1) v = some (falValue ℓ) := by
    rw [replayPath, replayStep, hℓ, ← hℓv]
    simp [falFix]
  have hstab := replayPath_fixed_stable (cs := cs) (ρ := ρ) (v := v) (b := falValue ℓ)
    (k + 1) (s - (k + 1)) hk1
  rw [show (k + 1) + (s - (k + 1)) = s from by omega] at hstab
  rw [hstab]; simp

/-- **The replay path fixes exactly the selected coordinates.** -/
theorem freeVars_replayPath_eq (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    freeVars (replayPath cs ρ s) = freeVars ρ \ replaySel cs ρ s := by
  ext v
  simp only [Finset.mem_sdiff, mem_freeVars]
  constructor
  · intro hv
    exact ⟨mem_freeVars.mp (freeVars_replayPath_subset cs ρ s (mem_freeVars.mpr hv)),
      fun hsel => replaySel_isSome hsel hv⟩
  · rintro ⟨hρ, hsel⟩
    rw [replayPath_eq_outside cs ρ s hsel]; exact hρ

/-- **Star bookkeeping.**  The end-state has `stars ρ − |replaySel|` free variables. -/
theorem stars_replayPath (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    stars (replayPath cs ρ s) + (replaySel cs ρ s).card = stars ρ := by
  have hsub := replaySel_subset_freeVars cs ρ s
  rw [stars, stars, freeVars_replayPath_eq, Finset.card_sdiff_of_subset hsub]
  have hle : (replaySel cs ρ s).card ≤ (freeVars ρ).card := Finset.card_le_card hsub
  omega

/-!
**Star bookkeeping proved.**  `stars (replayPath cs ρ s) + |replaySel cs ρ s| = stars ρ` — the
end-state's free-variable count drops by exactly the number of selected coordinates.  This is the
star relation the measure step's weight ratio (`pweight_ratio`) consumes.  The measure assembly is
the remaining probabilistic brick; not faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.stars_replayPath

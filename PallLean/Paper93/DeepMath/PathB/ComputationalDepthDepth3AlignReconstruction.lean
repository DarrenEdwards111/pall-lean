import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NoSkipReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EmptySkipWall

/-!
# Sharpening the satisfy-step switching core: the exact alignment hypothesis

The no-skip decoder (`reconstruction_no_skip`) discharges `ReconstructionCorrect` whenever *every*
replay block is non-empty.  Reading its proof, the all-blocks-non-empty hypothesis (`hns`) is used in
exactly one place: to get `groupBlocks (ungroupBlocks (replayLabel …)) = replayLabel …`.  Under
empty (skip) blocks this round-trip instead recovers only the non-empty blocks
(`tight_decode_replayLabel`: `= (replayLabel …).filter (·≠[])`), and `replayBlocks`'s positional `zip`
against `leafClauses` then **misaligns** — but *only* when an empty block precedes a non-empty one
(an interior skip).  When the empties are trailing, the zip is unchanged.

So the entire residual switching core reduces to a single combinatorial condition:

> `halign` — replaying the *filtered* (empties-dropped) label against `leafClauses` gives the same
> per-clause blocks as replaying the full label.

* `reconstruction_align` — `ReconstructionCorrect` holds under `halign` (replacing `hns`).  This is a
  **strict generalisation** of `reconstruction_no_skip`.
* `halign_of_no_skip` — `hns ⟹ halign` (the filter is the identity when no block is empty), so
  `reconstruction_no_skip` is recovered as the special case (`reconstruction_no_skip_via_align`).

## What remains (honest)

`halign` is exactly the irreducible Håstad confound the fences document: an interior empty (skip) block
shifts the `leafClauses` alignment, and the tight `(2w)^s` label cannot record where it sat
(`tight_pack_skip_invariant`).  `halign` fails precisely for restrictions whose deepest path falsifies
a clause that *also* received satisfy steps interleaved before a later satisfy clause — the end-state
cannot separate that from a clean skip.  This file does **not** discharge `halign`; it isolates it as
the sole remaining hypothesis.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The satisfy-step decoder under the exact alignment hypothesis.**  `ReconstructionCorrect` holds
whenever replaying the empties-dropped label against `leafClauses` reproduces the full replay blocks
(`halign`) — the precise condition `reconstruction_no_skip`'s `hns` was buying.  Strictly generalises
the no-skip regime. -/
theorem reconstruction_align {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad,
      (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s)
    (halign : ∀ ρ ∈ Bad,
      replayBlocks cs (deepestEnd cs F ρ) (replayLabel cs F ρ)
        = replayBlocks cs (deepestEnd cs F ρ)
            ((replayLabel cs F ρ).filter (fun b => !b.isEmpty))) :
    ReconstructionCorrect cs w s F Bad := by
  refine reconstruction_of_satSel_decoder hnf
    (fun π l => decodeSatSeq (replayBlocks cs π
      (SwitchingCounting.groupBlocks
        (List.map SwitchingCounting.finToNat (List.ofFn l)))).flatten)
    (fun ρ => SwitchingCounting.flatToLabel
      (SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ))))
    ?_
  intro ρ hρ
  have hofn : List.ofFn (SwitchingCounting.flatToLabel
        (SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)))
        : SwitchingCounting.PathLabel w s)
      = SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)) :=
    ofFn_flatToLabel (by rw [SwitchingCounting.toFinW, List.length_map]; exact hlen ρ hρ)
  have hfin : List.map SwitchingCounting.finToNat
        (SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)))
      = SwitchingCounting.ungroupBlocks (replayLabel cs F ρ) :=
    SwitchingCounting.finToNat_toFinW (hpos ρ hρ)
  have hgrp : SwitchingCounting.groupBlocks
        (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ))
      = (replayLabel cs F ρ).filter (fun b => !b.isEmpty) :=
    tight_decode_replayLabel cs F ρ
  show decodeSatSeq (replayBlocks cs (deepestEnd cs F ρ)
      (SwitchingCounting.groupBlocks (List.map SwitchingCounting.finToNat
        (List.ofFn (SwitchingCounting.flatToLabel
          (SwitchingCounting.toFinW w
            (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)))))))).flatten
      = deepestSatSel cs F ρ
  rw [hofn, hfin, hgrp, ← halign ρ hρ]
  exact replayBlocks_decodeSatSeq cs F ρ (hleaf ρ hρ)

/-- **`hns ⟹ halign`.**  If no replay block is empty, the empties-filter is the identity, so the
alignment hypothesis holds trivially. -/
theorem halign_of_no_skip {cs : List (Clause n)} {F : ℕ} {ρ : Fin n → Option Bool}
    (hns : ∀ b ∈ replayLabel cs F ρ, b ≠ []) :
    replayBlocks cs (deepestEnd cs F ρ) (replayLabel cs F ρ)
      = replayBlocks cs (deepestEnd cs F ρ)
          ((replayLabel cs F ρ).filter (fun b => !b.isEmpty)) := by
  have : (replayLabel cs F ρ).filter (fun b => !b.isEmpty) = replayLabel cs F ρ := by
    rw [List.filter_eq_self]
    intro b hb
    cases b with
    | nil => exact absurd rfl (hns _ hb)
    | cons x xs => rfl
  rw [this]

/-- `reconstruction_no_skip` recovered as the `halign`-special case (`hns ⟹ halign`). -/
theorem reconstruction_no_skip_via_align {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ Bad, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad,
      (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    ReconstructionCorrect cs w s F Bad :=
  reconstruction_align hnf hleaf hpos hlen (fun ρ hρ => halign_of_no_skip (hns ρ hρ))

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_align
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_no_skip_via_align

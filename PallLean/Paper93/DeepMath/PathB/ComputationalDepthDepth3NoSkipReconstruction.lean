import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestReplay
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction

/-!
# The interleaved satisfy-step decoder: `ReconstructionCorrect` for the no-skip regime

The reverse-induction decoder splits `deepestSel = decodedSel (deepestEnd …) ∪ deepestSatSel`: the
falsify-step variables come label-free from the end-state (`decodedSel`), and the **satisfy-step**
variables `deepestSatSel` are what the `(2w)^s` label encodes.  The pure-falsify regime
(`deepestSatSel = ∅`) was closed in `PureFalsifyReconstruction`; this file closes the genuinely
*interleaved* satisfy-step decoder for the **no-skip** regime — every processed clause contributes a
nonempty block, so satisfy and falsify steps may interleave freely as long as no clause is
*immediately* falsified.

The satisfy-step decoder is the proven replay decoder `decodeSatSeq ∘ flatten ∘ replayBlocks`
(`replayBlocks_decodeSatSeq`), with the `List (List ℕ)` replay label packed into `PathLabel w s` by
the established `flatToLabel ∘ toFinW ∘ ungroupBlocks` and *unpacked* by its round-trip inverses
(`ofFn_flatToLabel`, `finToNat_toFinW`, `groupBlocks_ungroupBlocks`).

* `reconstruction_no_skip` — discharges `ReconstructionCorrect` for the no-skip interleaved regime:
  `Dsat π l = decodeSatSeq (replayBlocks cs π (groupBlocks (map finToNat (ofFn l)))).flatten`.
* `deepest_no_skip_reconstruction_count` — hence `|Bad| ≤ |Short|·(2w)^s` via
  `deepest_switching_count_of_reconstruction` (the reconstruction-framework route to the same tight
  count proved directly by `deepest_noskip_tight_count`).

## What remains (honest)

`ReconstructionCorrect` is now discharged for **both** extreme regimes (pure-satisfy, pure-falsify)
**and** the interleaved no-skip regime.  The sole residual is the **empty-skip** case: clauses
falsified with *zero* satisfy steps interleaved among satisfy clauses.  Their empty blocks are not
encodable in the tight `(2w)^s` label, and the end-state cannot distinguish a 0-satisfy-step
falsified clause from a ≥1-satisfy-step one (both are falsified; `ρ`-true literals confound the true
ones) — the irreducible Håstad content, **not** faked here.  AC⁰/depth-3; `Depth3CollapseModel.collapse`
and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The interleaved satisfy-step decoder (no-skip).**  `ReconstructionCorrect` holds for the
no-skip regime: the satisfy-step decoder is the replay decoder, with the replay label packed into
`PathLabel w s` and recovered by the packing round-trips. -/
theorem reconstruction_no_skip {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ Bad, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad,
      (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
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
        (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)) = replayLabel cs F ρ :=
    SwitchingCounting.groupBlocks_ungroupBlocks _ (hns ρ hρ)
  show decodeSatSeq (replayBlocks cs (deepestEnd cs F ρ)
      (SwitchingCounting.groupBlocks (List.map SwitchingCounting.finToNat
        (List.ofFn (SwitchingCounting.flatToLabel
          (SwitchingCounting.toFinW w
            (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)))))))).flatten
      = deepestSatSel cs F ρ
  rw [hofn, hfin, hgrp]
  exact replayBlocks_decodeSatSeq cs F ρ (hleaf ρ hρ)

/-- **The no-skip tight count via the reconstruction framework.**  `ReconstructionCorrect` (no-skip)
plus the end-state landing in `Short` give `|Bad| ≤ |Short|·(2w)^s` — the same tight bound as
`deepest_noskip_tight_count`, now routed through `ReconstructionCorrect`. -/
theorem deepest_no_skip_reconstruction_count {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ Bad, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad,
      (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  deepest_switching_count_of_reconstruction hmem
    (reconstruction_no_skip hnf hleaf hns hpos hlen)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_no_skip
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_no_skip_reconstruction_count

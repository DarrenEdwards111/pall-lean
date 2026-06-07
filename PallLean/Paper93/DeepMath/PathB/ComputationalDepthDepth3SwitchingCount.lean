import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingInjective
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncLabel

/-!
# The depth-3 switching count, via the full-path reconstruction — branch only

The whole arc lands here: the full-path reconstruction yields `ReconstructionCorrect`, and the
codebase's `deepest_switching_count_of_reconstruction` then gives the tight count
`|Bad| ≤ |Short|·(2w)^s`.

* `deepestSel_recovered` — the selected set recovered from the leaf and the full path.
* `reconstructionCorrect_fullpath` — `ReconstructionCorrect cs w s F Bad`, with the full-path encoder
  `lab ρ = flatToLabel (toFinW w (deepestFullSeq cs F ρ))` and the composed recovery decoder, for a bad
  set whose paths have length `s` and positions `< w` (clause width).
* `fullpath_switching_count` — **the result**: `|Bad| ≤ |Short|·(2w)^s`.

This closes the depth-3 switching collapse's reconstruction obligation completely: the count is now a
theorem on proved components (no `sorry`).  `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The selected set recovered from the leaf and the full path. -/
theorem deepestSel_recovered (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hnf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    SwitchingCounting.decodedSel cs (deepestEnd cs F ρ)
        ∪ decodeSatSeq (fullReplaySatPar
            (recoverStream cs (deepestEnd cs F ρ) ((deepestFullSeq cs F ρ).map Prod.fst)
              (fun _ => none))
            (deepestFullSeq cs F ρ))
      = deepestSel cs F ρ := by
  rw [deepestSatSeq_reconstructed cs F ρ hnf hleaf,
      ← deepestSatSel_eq_decodeSatSeq cs F ρ,
      decodedSel_union_satSel_eq_deepestSel hnf]

/-- **`ReconstructionCorrect` via the full path.**  For a bad set whose full paths have length `s` and
positions `< w`, the full-path encoder and the composed recovery decoder satisfy the reconstruction
invariant. -/
theorem reconstructionCorrect_fullpath (cs : List (Clause n)) (w s F : ℕ) [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    ReconstructionCorrect cs w s F Bad := by
  refine ⟨fun ρ => SwitchingCounting.flatToLabel (toFinW w (deepestFullSeq cs F ρ)),
    fun π lbl => SwitchingCounting.decodedSel cs π
      ∪ decodeSatSeq (fullReplaySatPar
          (recoverStream cs π (((List.ofFn lbl).map finToNat).map Prod.fst) (fun _ => none))
          ((List.ofFn lbl).map finToNat)),
    fun ρ hρ => ?_⟩
  have hround : (List.ofFn (SwitchingCounting.flatToLabel
        (toFinW w (deepestFullSeq cs F ρ)) : SwitchingCounting.PathLabel w s)).map finToNat
      = deepestFullSeq cs F ρ := by
    rw [ofFn_flatToLabel (by rw [toFinW, List.length_map]; exact hlen ρ hρ)]
    exact finToNat_toFinW (hpos ρ hρ)
  show SwitchingCounting.decodedSel cs (deepestEnd cs F ρ)
      ∪ decodeSatSeq (fullReplaySatPar
          (recoverStream cs (deepestEnd cs F ρ)
            (((List.ofFn (SwitchingCounting.flatToLabel
              (toFinW w (deepestFullSeq cs F ρ)) : SwitchingCounting.PathLabel w s)).map finToNat).map
              Prod.fst) (fun _ => none))
          ((List.ofFn (SwitchingCounting.flatToLabel
            (toFinW w (deepestFullSeq cs F ρ)) : SwitchingCounting.PathLabel w s)).map finToNat))
      = deepestSel cs F ρ
  rw [hround]
  exact deepestSel_recovered cs F ρ (hnf ρ hρ) (hleaf ρ hρ)

/-- **The tight depth-3 switching count, fully proved.**  A bad set whose deepest end-states land in
`Short`, with full paths of length `s` and positions `< w`, has `|Bad| ≤ |Short|·(2w)^s`. -/
theorem fullpath_switching_count (cs : List (Clause n)) (w s F : ℕ) [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  deepest_switching_count_of_reconstruction hmem
    (reconstructionCorrect_fullpath cs w s F hnf hleaf hlen hpos)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.fullpath_switching_count

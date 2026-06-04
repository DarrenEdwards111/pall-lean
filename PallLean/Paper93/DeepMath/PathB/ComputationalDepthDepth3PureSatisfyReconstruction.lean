import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFlatLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncLabel

/-!
# Pure-satisfy regime: `ReconstructionCorrect` via the `PathLabel` coercion

The final step: package the pure-satisfy position recovery into the `(2w)^s` label type
`PathLabel w s` and feed `reconstruction_of_satSel_decoder`, yielding `ReconstructionCorrect` for the
pure-satisfy bad set.  No new mathematics — only the index→`Fin w` coercion (`natToFin`) and the
list↔`Fin s`-function packing (`flatToLabel`), both already in the arc.

* `ofFn_flatToLabel` — the packing round-trips: `List.ofFn (flatToLabel L) = L` on length-`s` lists.
* `reconstructionCorrect_pure_satisfy` — **the result.**  For a bad set of pure-satisfy restrictions
  (no falsify step, clean active clause, leaf unsatisfied, exactly `s` satisfy positions, each `< w`),
  `ReconstructionCorrect cs w s F Bad` holds — with the explicit decoder
  `π, label ↦ decodeSatPos (activeTerm cs π) (positions of label)` and encoder
  `ρ ↦ flatToLabel (natToFin-coerced deepestSatPos)`.

Combined with `deepest_switching_count_of_reconstruction`, this gives the tight
`|Bad| ≤ |Short|·(2w)^s` switching count for the pure-satisfy regime, entirely on proved components.
The listed conditions are the genuine defining properties of the pure-satisfy bad set, not gaps.  The
general interleaved case (falsify steps moving the active clause) is unchanged and not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The flat packing round-trips on length-`s` lists: `List.ofFn (flatToLabel L) = L`. -/
theorem ofFn_flatToLabel {w s : ℕ} [NeZero w] {L : List (Fin w × Bool)} (hL : L.length = s) :
    List.ofFn (SwitchingCounting.flatToLabel L : SwitchingCounting.PathLabel w s) = L := by
  apply List.ext_getElem
  · rw [List.length_ofFn, hL]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    simp only [SwitchingCounting.flatToLabel]
    rw [List.getElem?_eq_getElem h2]
    rfl

/-- **Pure-satisfy `ReconstructionCorrect` via the `(2w)^s` label.**  A bad set of pure-satisfy
restrictions — each falsifying nothing, with a clean active clause, an unsatisfied leaf, exactly `s`
satisfy positions, all `< w` — satisfies `ReconstructionCorrect cs w s F Bad`.  The decoder reads the
constant clause off the end-state and decodes the labelled positions through it. -/
theorem reconstructionCorrect_pure_satisfy {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hact : ∀ ρ ∈ Bad, ∃ T, SwitchingCounting.activeTerm cs ρ = some T ∧ CleanClause T)
    (hpure : ∀ ρ ∈ Bad, deepestFalSel cs F ρ = ∅)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestSatPos cs F ρ).length = s)
    (hlt : ∀ ρ ∈ Bad, ∀ p ∈ deepestSatPos cs F ρ, p < w) :
    ReconstructionCorrect cs w s F Bad := by
  refine reconstruction_of_satSel_decoder hnf
    (fun π label => match SwitchingCounting.activeTerm cs π with
      | some T => decodeSatPos T ((List.ofFn label).map (fun pb => pb.1.val))
      | none => ∅)
    (fun ρ => SwitchingCounting.flatToLabel
      ((deepestSatPos cs F ρ).map (fun p => (SwitchingCounting.natToFin w p, true))))
    ?_
  intro ρ hρ
  obtain ⟨T, hactT, hcleanT⟩ := hact ρ hρ
  have hleafT : SwitchingCounting.activeTerm cs (deepestEnd cs F ρ) = some T :=
    activeTerm_deepestEnd_pure_satisfy cs hcleanT F ρ hactT (hpure ρ hρ) (hleaf ρ hρ)
  -- length of the coerced position list
  have hL : ((deepestSatPos cs F ρ).map
      (fun p => (SwitchingCounting.natToFin w p, true))).length = s := by
    rw [List.length_map]; exact hlen ρ hρ
  -- the decoded position list is exactly `deepestSatPos`
  have hmap : (List.ofFn (SwitchingCounting.flatToLabel
        ((deepestSatPos cs F ρ).map (fun p => (SwitchingCounting.natToFin w p, true)))
        : SwitchingCounting.PathLabel w s)).map (fun pb => pb.1.val) = deepestSatPos cs F ρ := by
    rw [ofFn_flatToLabel hL, List.map_map]
    rw [List.map_congr_left (g := id) (fun p hp => by
      simp only [Function.comp_apply, id_eq]
      exact SwitchingCounting.natToFin_val (hlt ρ hρ p hp))]
    exact List.map_id _
  -- evaluate the decoder
  simp only [hleafT]
  rw [hmap]
  exact (deepestSatSel_eq_decode_pure_satisfy cs hcleanT F ρ hactT (hpure ρ hρ) (hleaf ρ hρ)).symm

/-- **The tight `(2w)^s` switching count for the pure-satisfy regime.**  Combining
`reconstructionCorrect_pure_satisfy` with `deepest_switching_count_of_reconstruction`: a pure-satisfy
bad set whose deepest end-states land in `Short` has `|Bad| ≤ |Short|·(2w)^s`.  This is the deepest
branch's tight switching count, fully proved for the pure-satisfy regime. -/
theorem pure_satisfy_switching_count {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hact : ∀ ρ ∈ Bad, ∃ T, SwitchingCounting.activeTerm cs ρ = some T ∧ CleanClause T)
    (hpure : ∀ ρ ∈ Bad, deepestFalSel cs F ρ = ∅)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestSatPos cs F ρ).length = s)
    (hlt : ∀ ρ ∈ Bad, ∀ p ∈ deepestSatPos cs F ρ, p < w) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  deepest_switching_count_of_reconstruction hmem
    (reconstructionCorrect_pure_satisfy hnf hact hpure hleaf hlen hlt)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstructionCorrect_pure_satisfy
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pure_satisfy_switching_count

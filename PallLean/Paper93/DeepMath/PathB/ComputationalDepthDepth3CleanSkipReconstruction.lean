import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AlignReconstruction

/-!
# Interior (clean) skips: the satisfy-step decoder reinserts empty blocks from the end-state

`reconstruction_align` needed `halign`, which is *false* under an interior empty block: the tight
`(2w)^s` packing drops empty blocks, so `replayBlocks` re-pairs `leafClause_k` with the `k`-th
*non-empty* block instead of its own (`tight_pack_skip_invariant`).  The fix for **clean** interior
skips — where each empty block is exactly a *falsified* leaf clause (no satisfy steps) — is to
**reinsert** the empty blocks at the falsified-clause positions, read off the end-state `π`.

`reinsert fb cls blocks` walks the leaf clauses `cls`: it emits `[]` (a skip) at each clause with
`fb` true (falsified at `π`), and otherwise consumes the next non-empty block.  Under the *clean-skip*
hypothesis `hskip` — `deepestSatPositions C = [] ↔ C falsified at π`, for every leaf clause `C` — this
reconstructs the full `replayLabel` exactly, so the decoder recovers `deepestSatSel`.

* `reinsert` / `reinsert_map_filter` — the reinsertion and its correctness as a list identity.
* `reconstruction_clean_skip` — `ReconstructionCorrect` under `hskip` (allows **interior** empty
  blocks, unlike `reconstruction_no_skip`).

## What remains (honest)

`hskip` excludes exactly the irreducible Håstad confound: a clause *falsified at the leaf that also
received satisfy steps* (a satisfy step then a falsify step on the same clause) has a **non-empty**
block yet is falsified — indistinguishable at the end-state from a clean skip, so its empties cannot
be reinserted correctly.  This file does **not** discharge that confound; it closes the
*confound-free* interior-skip regime.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Reinsert empty (skip) blocks at the `fb`-true clauses, consuming a non-empty block for each
`fb`-false clause. -/
def reinsert (fb : Clause n → Bool) : List (Clause n) → List (List ℕ) → List (List ℕ)
  | [], _ => []
  | C :: cls', blocks =>
      if fb C = true then [] :: reinsert fb cls' blocks
      else blocks.headD [] :: reinsert fb cls' blocks.tail

/-- **Reinsertion correctness (list identity).**  If every clause's block is empty iff `fb` is true,
reinserting the empties-dropped blocks recovers the full `cls.map g`. -/
theorem reinsert_map_filter (fb : Clause n → Bool) (g : Clause n → List ℕ) :
    ∀ (cls : List (Clause n)), (∀ C ∈ cls, (g C = [] ↔ fb C = true)) →
      reinsert fb cls ((cls.map g).filter (fun b => !b.isEmpty)) = cls.map g := by
  intro cls
  induction cls with
  | nil => intro _; rfl
  | cons C cls' ih =>
    intro h
    have hiff : g C = [] ↔ fb C = true := h C (List.mem_cons_self ..)
    have hrec : ∀ C' ∈ cls', (g C' = [] ↔ fb C' = true) :=
      fun C' hC' => h C' (List.mem_cons_of_mem C hC')
    by_cases hfb : fb C = true
    · have hgC : g C = [] := hiff.mpr hfb
      rw [List.map_cons, List.filter_cons, hgC]
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
      rw [reinsert, if_pos hfb, ih hrec]
    · have hgC : g C ≠ [] := fun hc => hfb (hiff.mp hc)
      have hne : (!(g C).isEmpty) = true := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false]
        exact List.isEmpty_eq_false_iff.mpr hgC
      rw [List.map_cons, List.filter_cons, if_pos hne, reinsert, if_neg hfb,
        List.headD_cons, List.tail_cons, ih hrec]

/-- Reinsertion recovers `replayLabel` exactly, under the clean-skip hypothesis. -/
theorem reinsert_filter_eq_replayLabel {cs : List (Clause n)} {F : ℕ}
    {ρ : Fin n → Option Bool}
    (hskip : ∀ C ∈ leafClauses cs (deepestEnd cs F ρ),
      (deepestSatPositions cs F ρ C = [] ↔ SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = true)) :
    reinsert (fun C => SwitchingCounting.termFalsified (deepestEnd cs F ρ) C)
        (leafClauses cs (deepestEnd cs F ρ))
        ((replayLabel cs F ρ).filter (fun b => !b.isEmpty))
      = replayLabel cs F ρ :=
  reinsert_map_filter _ (deepestSatPositions cs F ρ) (leafClauses cs (deepestEnd cs F ρ)) hskip

/-- **The clean-skip satisfy-step decoder.**  `ReconstructionCorrect` holds when every empty replay
block coincides with a clause falsified at the end-state (`hskip`): the decoder reinserts the empty
blocks at those positions, recovering the alignment that interior skips otherwise destroy. -/
theorem reconstruction_clean_skip {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad,
      (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s)
    (hskip : ∀ ρ ∈ Bad, ∀ C ∈ leafClauses cs (deepestEnd cs F ρ),
      (deepestSatPositions cs F ρ C = [] ↔
        SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = true)) :
    ReconstructionCorrect cs w s F Bad := by
  refine reconstruction_of_satSel_decoder hnf
    (fun π l => decodeSatSeq (replayBlocks cs π
      (reinsert (fun C => SwitchingCounting.termFalsified π C) (leafClauses cs π)
        (SwitchingCounting.groupBlocks
          (List.map SwitchingCounting.finToNat (List.ofFn l))))).flatten)
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
  dsimp only
  rw [hofn, hfin, tight_decode_replayLabel, reinsert_filter_eq_replayLabel (hskip ρ hρ)]
  exact replayBlocks_decodeSatSeq cs F ρ (hleaf ρ hρ)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reinsert_map_filter
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_clean_skip

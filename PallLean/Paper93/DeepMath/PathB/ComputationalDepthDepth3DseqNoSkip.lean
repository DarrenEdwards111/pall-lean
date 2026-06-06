import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqPureSatisfy

/-!
# `Dseq` correctness in the no-skip regime (branch `razborov-recoverRho-wip`)

The **no-skip** regime: every leaf clause receives a *nonempty* satisfy block (no empty/skip block).  In
this regime the general round-trip `ungroupBlocks ↔ replayBlocksFlat` holds clause-by-clause, so the
concrete decoder `Dseq` (with the `replayLabel`-based Side-B encoder) reproduces `deepestSatSeq`.

* `takeBlock_markLast_append` — `takeBlock` splits off exactly the first `markLast` block (its only
  `true` bit is at the end), leaving the remainder untouched.
* `replayBlocksFlat_ungroup_pairs` — **the round-trip**: walking the clauses of a list of
  `(clause, nonempty block)` pairs over `toFinW (ungroupBlocks blocks)` emits exactly the per-clause
  position blocks.
* `Dseq_correct_no_skip` — **the result**: with the `replayLabel` encoder, all blocks nonempty, and the
  genuine no-skip structural fact (`deepestSatSeq = ⋃ leaf-clause blocks`), `Dseq` recovers
  `deepestSatSeq`.

Clean-skip (interior *empty* blocks) is **not** covered: `Dseq` walks every leaf clause and would
mis-consume tokens at an empty block.  Handling it needs `Dseq` to skip empty-block clauses via the
end-state — that is the confound-adjacent step, deferred.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `takeBlock` splits off the first `markLast` block: for `b ≠ []`, the coerced `markLast b` (whose
only `true` bit is on its last element) is consumed whole, leaving `rest`. -/
theorem takeBlock_markLast_append {w : ℕ} [NeZero w] :
    ∀ (b : List ℕ), b ≠ [] → ∀ (rest : List (Fin w × Bool)),
      takeBlock (toFinW w (markLast b) ++ rest) = (toFinW w (markLast b), rest)
  | [], hb, _ => absurd rfl hb
  | [_], _, _ => rfl
  | x :: y :: xs, _, rest => by
      show (match takeBlock (toFinW w (markLast (y :: xs)) ++ rest) with
            | (b, r) => ((SwitchingCounting.natToFin w x, false) :: b, r))
          = ((SwitchingCounting.natToFin w x, false) :: toFinW w (markLast (y :: xs)), rest)
      rw [takeBlock_markLast_append (y :: xs) (by simp) rest]

/-- **The `ungroupBlocks ↔ replayBlocksFlat` round-trip on nonempty blocks.**  Walking the clauses of a
list of `(clause, block)` pairs (each block nonempty, indices `< w`) over the coerced ungrouped label
emits exactly the per-clause position blocks. -/
theorem replayBlocksFlat_ungroup_pairs {w : ℕ} [NeZero w] :
    ∀ (pairs : List (Clause n × List ℕ)),
      (∀ cb ∈ pairs, cb.2 ≠ []) → (∀ cb ∈ pairs, ∀ p ∈ cb.2, p < w) →
      replayBlocksFlat (pairs.map Prod.fst) (toFinW w (ungroupBlocks (pairs.map Prod.snd)))
        = pairs.flatMap (fun cb => cb.2.map (fun p => (cb.1, p)))
  | [], _, _ => by simp [ungroupBlocks, replayBlocksFlat, toFinW]
  | (C, b) :: ps, hne, hlt => by
      have hbne : b ≠ [] := hne (C, b) List.mem_cons_self
      simp only [List.map_cons, ungroupBlocks]
      rw [show toFinW w (markLast b ++ ungroupBlocks (ps.map Prod.snd))
            = toFinW w (markLast b) ++ toFinW w (ungroupBlocks (ps.map Prod.snd)) by
          rw [toFinW, toFinW, toFinW, List.map_append]]
      have hsplit : replayBlocksFlat (C :: ps.map Prod.fst)
            (toFinW w (markLast b) ++ toFinW w (ungroupBlocks (ps.map Prod.snd)))
          = (takeBlock (toFinW w (markLast b)
                ++ toFinW w (ungroupBlocks (ps.map Prod.snd)))).1.map (fun t => (C, (t.1 : ℕ)))
              ++ replayBlocksFlat (ps.map Prod.fst)
                  (takeBlock (toFinW w (markLast b)
                    ++ toFinW w (ungroupBlocks (ps.map Prod.snd)))).2 := by
        rw [replayBlocksFlat]
      rw [hsplit, takeBlock_markLast_append b hbne,
          map_toFinW_markLast b C (hlt (C, b) List.mem_cons_self),
          replayBlocksFlat_ungroup_pairs ps (fun cb hcb => hne cb (List.mem_cons_of_mem _ hcb))
            (fun cb hcb => hlt cb (List.mem_cons_of_mem _ hcb)),
          List.flatMap_cons]

/-- **`Dseq` reproduces `deepestSatSeq` in the no-skip regime.**  Every leaf clause has a nonempty
satisfy block (`hns`); positions are `< w` (`hlt`); the label has length `s` (`hlen`); and
`deepestSatSeq` is the concatenation of the per-leaf-clause blocks (`hseq`, the genuine no-skip
structural characterisation).  Then the concrete `Dseq`, with the `replayLabel`-based encoder, recovers
`deepestSatSeq`. -/
theorem Dseq_correct_no_skip {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {ρ : Fin n → Option Bool}
    (hns : ∀ C ∈ leafClauses cs (deepestEnd cs F ρ), deepestSatPositions cs F ρ C ≠ [])
    (hlt : ∀ C ∈ leafClauses cs (deepestEnd cs F ρ), ∀ p ∈ deepestSatPositions cs F ρ C, p < w)
    (hlen : (ungroupBlocks (replayLabel cs F ρ)).length = s)
    (hseq : deepestSatSeq cs F ρ
      = (leafClauses cs (deepestEnd cs F ρ)).flatMap
          (fun C => (deepestSatPositions cs F ρ C).map (fun p => (C, p)))) :
    Dseq cs (deepestEnd cs F ρ)
        (SwitchingCounting.flatToLabel
            (toFinW w (ungroupBlocks (replayLabel cs F ρ))) : SwitchingCounting.PathLabel w s)
      = deepestSatSeq cs F ρ := by
  have hrl : replayLabel cs F ρ
      = (leafClauses cs (deepestEnd cs F ρ)).map (deepestSatPositions cs F ρ) := rfl
  -- the pair list: each leaf clause with its position block
  set pairs := (leafClauses cs (deepestEnd cs F ρ)).map
    (fun C => (C, deepestSatPositions cs F ρ C)) with hpairs
  have hpf : pairs.map Prod.fst = leafClauses cs (deepestEnd cs F ρ) := by
    rw [hpairs, List.map_map,
      show (Prod.fst ∘ fun C : Clause n => (C, deepestSatPositions cs F ρ C)) = id from rfl,
      List.map_id]
  have hps : pairs.map Prod.snd = replayLabel cs F ρ := by
    rw [hrl, hpairs, List.map_map,
      show (Prod.snd ∘ fun C : Clause n => (C, deepestSatPositions cs F ρ C))
        = deepestSatPositions cs F ρ from rfl]
  have hne : ∀ cb ∈ pairs, cb.2 ≠ [] := by
    intro cb hcb
    rw [hpairs, List.mem_map] at hcb
    obtain ⟨C, hC, rfl⟩ := hcb
    exact hns C hC
  have hlt' : ∀ cb ∈ pairs, ∀ p ∈ cb.2, p < w := by
    intro cb hcb
    rw [hpairs, List.mem_map] at hcb
    obtain ⟨C, hC, rfl⟩ := hcb
    exact hlt C hC
  have key := replayBlocksFlat_ungroup_pairs pairs hne hlt'
  rw [hpf, hps] at key
  rw [Dseq, ofFn_flatToLabel (by rw [toFinW, List.length_map]; exact hlen), key, hseq, hpairs,
      List.flatMap_map]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Dseq_correct_no_skip

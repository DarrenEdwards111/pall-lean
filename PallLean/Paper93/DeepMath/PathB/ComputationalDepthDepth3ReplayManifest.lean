import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyDepth

/-!
# Deepest-branch replay arc: manifest

A machine-checked index of the replay decoder for the *general interleaved* deepest branch — the
construction that recovers the deepest selected set (and hence counts the bad set) when falsify and
satisfy steps interleave.  Every `#check` below is a proved theorem (clean axioms, no `sorry`).

## The decoder, in stages

* **Stage 1 — definition + shape.**  `replayBlocks` walks the end-state-readable clauses
  (`leafClauses`) zipped with per-clause position blocks, emitting nonempty `(clause, position)`
  blocks and skipping empty (immediately-falsified) clauses.  `replayBlocks_ne_nil`,
  `replayBlocks_block_entry_mem_leafClauses` give it the same shape as the target.
* **Stage 2 — one step.**  `replayAux_cons_empty` (skip), `replayAux_cons_nonempty` (emit).
* **Stage 3a — reconstruction round-trip.**  `replayAux_map_eq`: the decoder reconstructs the nonempty
  blocks of a `(clause, positions)` list, skipping empties.
* **Stage 3b-i — concrete encoder.**  `replayBlocks_eq_filter`: with the encoder `replayLabel`, the
  decoder output is a filter-map of the entry list.
* **Stage 3b-ii — soundness (alignment dissolved).**  `decodeSatSeq` is a `toFinset`, so order is
  irrelevant; `replayBlocks_flatten_mem` matches the pair *set*, giving `replayBlocks_decodeSatSeq`:
  the decoder recovers `deepestSatSel`.
* **Stage 4 — determinism.**  `replay_inj`: the end-state and label determine `ρ`.

## The theorem inventory (what is proved)

1. **Pure-satisfy tight `(2w)^s`** — `pure_satisfy_switching_count_depth`,
   `reconstructionCorrect_pure_satisfy`: when the branch has no falsify step the recovery is
   end-to-end, `|Bad| ≤ |Short| · (2w)^s` with the size condition `canonicalDT.depth = s`.
2. **General no-skip tight `(2w)^s`** — `deepest_noskip_tight_count` and its structural forms
   `_width` (clause width `≤ w`), `_struct` (label records `s` positions), `_satsteps` (canonical
   `(deepestSatSeq …).length = s`): interleaved falsify steps allowed, provided no clause is
   immediately falsified.
3. **Loose general `2^n`** — `deepest_loose_count`: fully general (only "ρ falsifies nothing"), label
   = the recovered set; validates the whole architecture end-to-end.
4. **Satisfy-count depth bound `s ≤ depth`** — `deepestSatSeq_length_le_depth`: the label cost
   `(2w)^s` is at most `(2w)^depth`; the counts are sharp relative to the switching quantity.

## The empty-skip wall (NOT claimed)

The **full-general tight** count — interleaved branches *with* immediately-falsified (empty-block)
clauses, packed into the fixed `(2w)^s` label `PathLabel w s` — is **not** proved: the tight label
cannot encode which leaf clauses are skipped.  Soundness, determinism, the loose count, and the
no-skip tight count are all established above; only this empty-block packing remains, and it is **not**
faked.  Ceiling: AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- Stage 1: definition + shape.
#check @Depth3.replayBlocks
#check @Depth3.replayBlocks_ne_nil
#check @Depth3.replayBlocks_block_entry_mem_leafClauses

-- Stage 2: one replay step.
#check @Depth3.replayAux_cons_empty
#check @Depth3.replayAux_cons_nonempty

-- Stage 3a: reconstruction round-trip.
#check @Depth3.replayAux_map_eq

-- Stage 3b-i: concrete encoder.
#check @Depth3.replayBlocks_eq_filter

-- Stage 3b-ii: soundness (alignment dissolved by order-insensitivity).
#check @Depth3.replayBlocks_flatten_mem
#check @Depth3.replayBlocks_decodeSatSeq

-- Stage 4: determinism.
#check @Depth3.replay_inj

-- Inventory 1: pure-satisfy tight (2w)^s (end-to-end, size condition = canonicalDT.depth).
#check @Depth3.reconstructionCorrect_pure_satisfy
#check @Depth3.pure_satisfy_switching_count_depth

-- Inventory 2: general no-skip tight (2w)^s (structural conditions).
#check @Depth3.deepest_noskip_tight_count
#check @Depth3.deepest_noskip_tight_count_width
#check @Depth3.deepest_noskip_tight_count_struct
#check @Depth3.deepest_noskip_tight_count_satsteps

-- Inventory 3: loose general 2^n (fully general).
#check @Depth3.deepest_loose_count

-- Inventory 4: satisfy-count depth bound s ≤ depth (sharpness).
#check @Depth3.deepestSatSeq_length_le_depth

end PallLean.Paper93.DeepMath.PathB

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAdditiveSheetCrossBlock

/-!
# Manifest: the block-DT holographic switching arc (branch `razborov-recoverRho-wip`)

A machine-checked index of the block decision-tree holographic switching count.  Every `#check` is a
proved theorem with clean axioms (no `sorry`, no `native_decide`).

## The arc

The binary canonical DT kills a term in one query, so the satisfying encoding does not compose
(`allfree_step0_fails` no-go).  On the **block** model (one whole active term per block), the
satisfying/killing duality is natural, and the holographic boundary `blockEncode` + tiny stars-pattern
`blockMasks` determines the hidden active-clause stream — **without** clause identity and **without** the
`2^|cs|` live-sublist factor.

* Brick 1 — `killTerm`: the term-falsifying step (dual of `satExtendTerm`).
* Brick 2 — `blockEnd` / `blockStream`: the deterministic block descent.
* Brick 3 — `blockEncode`: the satisfying boundary encoding.
* Brick 4 — `blockEncode_firstSat`: the boundary's first satisfied term is the active term.
* Brick 5 — `blockEncode_advance`, `block_recovery`: the label-aware peel recovers the whole stream.
* Brick 6 — `block_injective`: `ρ ↦ (blockEncode, blockMasks)` is injective.
* Brick 7 — `block_count`: `|Bad| ≤ |Short| · |Labels|`.
* Brick 8 — `stars_blockEncode`, `stars_blockEncode_le`, `block_switching_count`: star conservation,
  the leaf-depth bound `stars ≤ K-s`, and the quantitative count.

## Open piece (honest)

The tight label bound `|Labels| ≤ (2^w)^s` (no `|cs|` factor) requires re-encoding `blockMasks` from
global-variable masks to per-block in-clause positions (`< w`) — the depth-3 `PathLabel` analogue.
Until then `block_switching_count` carries `Labels` as a parameter.  AC⁰/depth-3; not P≠NP-strength.

## Audit artifact (independent)

`additive_sheet_cross_block_vanish`: the additive sheet `Q⁺ = 1 - ∑_C V_C²` has vanishing cross-block
mixed partials — the formal reason its SPDP rank collapses (pinning the `p-vs-np1.pdf` `Q⁺ → Q^×` flaw).
-/

namespace PallLean.Paper93.DeepMath.PathB

-- Brick 1: kill operation
#check @Depth3.killTerm
#check @Depth3.killTerm_extends
#check @Depth3.killTerm_falsifies

-- Brick 2: block descent
#check @Depth3.blockEnd
#check @Depth3.blockStream
#check @Depth3.blockEnd_extends
#check @Depth3.blockStream_length_le

-- Brick 3: satisfying boundary encoding
#check @Depth3.blockEncode
#check @Depth3.blockEncode_extends

-- Brick 4: first-satisfied recovery (per block)
#check @Depth3.blockEncode_sat_term
#check @Depth3.blockEncode_firstSat

-- Brick 5: advance + end-to-end recovery
#check @Depth3.blockEncode_advance
#check @Depth3.blockMasks
#check @Depth3.blockPeel
#check @Depth3.block_recovery

-- Brick 6: injection
#check @Depth3.recoverRho
#check @Depth3.blockEncode_recover
#check @Depth3.block_injective

-- Brick 7: holographic count
#check @Depth3.block_count

-- Brick 8: star conservation, leaf-depth bound, quantitative count
#check @Depth3.stars_blockEncode
#check @Depth3.maskedVars
#check @Depth3.blockStream_length_le_maskedVars
#check @Depth3.stars_blockEncode_le
#check @Depth3.card_stars_le
#check @Depth3.block_switching_count

-- Audit artifact: additive-sheet cross-block vanishing (the p-vs-np1 flaw, formalized)
#check @AdditiveSheetAudit.vars_pderiv_le
#check @AdditiveSheetAudit.additive_sheet_cross_block_vanish

end PallLean.Paper93.DeepMath.PathB

import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockTightCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCircuitCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeSwap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Circuit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitDepthReduction
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
* Brick 9 — `BlockPathLabel`, `card_blockPathLabel`: the **compact** in-clause label type and its
  size `(2^w)^s` (the canonical switching base, no `|cs|` factor).
* Brick 10 — `freePosOf` / `posMaskOf` / `posMaskOf_freePosOf` (compatibility), `compactMasks` /
  `blockPeelC` / `block_recovery_compact` / `blockMasks_eq_zipWith` (compact recovery),
  `block_injective_compact`, and **`block_switching_count_tight`**: the tight count
  `|Bad| ≤ |{σ : stars σ ≤ K-s}| · (2^w)^s`.

## Closed piece

The tight label bound `|Labels| ≤ (2^w)^s` (no `|cs|` factor) is now **proved**: `blockMasks` is
re-encoded from global-variable masks to per-block in-clause positions (`< w`, the depth-3 `PathLabel`
analogue) via `compactMasks`, recovered by `blockMasks_eq_zipWith` + `block_recovery_compact`, and the
injection `ρ ↦ (blockEncode ρ, compactMasks ρ)` lands in `Short ×ˢ BlockPathLabel w s`.  The headline
`block_switching_count_tight` carries no `Labels` parameter.  AC⁰/depth-3; not P≠NP-strength.

## Count → probability (brick 11)

`block_switching_prob_le` turns the count into a fraction under the uniform distribution on the
`K`-star shell `Ω = {σ : stars σ = K}`: `Pr_Ω[depth ≥ s] ≤ (∑_{j≤K-s} C(n,j)2^(n-j))·(2^w)^s / |Ω|`.
`shell_ratio_nat` is the per-star geometric gain `C(n,K-s)·2^(n-K+s)·(n-K+1)^s ≤ C(n,K)·2^(n-K)·(2K)^s`
(`≈ (2K/(n-K+1))^s`, the Håstad `p^s`).

## Closed Håstad form (brick 12 — geometric-tail collapse, now closed)

`block_switching_prob_closed`: in the `2K < n-K+1` regime (`r = 2K/(n-K+1) < 1`, i.e. `p < 1/3`),
`Pr_Ω[block-DT depth ≥ s] ≤ (2^w · 2K/(n-K+1))^s / (1 - 2K/(n-K+1))`.  The cumulative shell sum is
collapsed via `term_ratio_q` (per-shell ℚ ratio), `sum_range_reflect` (reindex `j ↦ K-j`), and
`geom_tail_le` (`∑ r^i ≤ 1/(1-r)`, proved from the partial-sum identity, no `GeomSum` dependency).

## Circuit collapse (brick 13 — probabilistic method)

`circuit_collapse_exists`: running the descent with fuel `s` (so `length = s ⟺ depth ≥ s`), the
union bound `G · |Short| · (2^w)^s < |Ω| = C(n,K)2^(n-K)` yields a *single* restriction in the
`K`-star shell under which **every** bottom gate's canonical block-DT is shallow (depth `< s`) — the
restriction that drops circuit depth by collapsing all bottom DNFs at once.  `exists_avoiding_all` is
the reusable union-bound existence core (`card_biUnion_le` + `card_le_card_sdiff_add_card`).

## DT → CNF/DNF representation swap (brick 14)

`DTree.dnf_cnf_swap`: a self-contained binary decision tree is simultaneously a width-`≤ depth` DNF
(`toDNF`, accepting paths) and a width-`≤ depth` CNF (`toCNF`, rejecting paths) computing the same
function (`eval_eq_dnf`, `eval_eq_cnf`).  Re-expressing the shallow DT from brick 13 as a CNF is the
`∨∧ ↦ ∧∨` swap that merges the bottom two circuit layers — one depth-reduction step.  Clean axioms
`[propext, Quot.sound]` (no `Classical.choice`).  This is genuine AC⁰ depth-reduction machinery; it
tops out at AC⁰ and is not P≠NP-strength.

## One depth-reduction step d → d-1 (brick 15)

`DTree.depth_reduction_step`: the second half of depth reduction — the associativity collapse.  An
unbounded-fan-in `AND` of depth-`≤ d` decision-tree gates is a *single* width-`≤ d` CNF
(`flatMap toCNF`, `bigAnd_eq_cnf`), and dually `OR` of such gates is a single width-`≤ d` DNF
(`flatMap toDNF`, `bigOr_eq_dnf`).  The gate layer is absorbed into the top connective (`AND`-of-`AND`s
flattens), removing one alternation level — `d → d-1`.  Composed with the swap (brick 14) this is a full
switching depth-reduction step.  Clean `[propext, Quot.sound]`; AC⁰ ceiling, not P≠NP-strength.

## Concrete circuit datatype + depth-reduction theorem (bricks 16–17)

`Circ` is an explicit alternating AC⁰ circuit (`lit`/`and`/`or`, unbounded fan-in) with `eval` and
`height`.  `bigAnd_flatten_eval` / `bigOr_flatten_eval` are the iterated same-type collapse; `toCirc`
realises a shallow `DTree` as a depth-2 width-bounded CNF circuit (the swap, on circuits).

`DTree.and_trees_depth_reduction` is **the formal `d → d-1` theorem over the real datatype**: under a
good restriction (every bottom gate a shallow DT of depth `≤ w`), an `AND` over those gates is
equivalent to a *single* CNF circuit (`cnfToCirc (flatMap toCNF)`) whose every bottom `OR`-clause has
fan-in `≤ w` (`and_trees_cnf_width`) and whose alternation height is `≤ 2` (`and_trees_height_le`) — one
level shallower with controlled bottom width.  Iterating with a fresh good restriction per round
(`circuit_collapse_exists`) drives the depth down.  AC⁰ ceiling; not P≠NP-strength.

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

-- Brick 9: compact in-clause label type and its size (2^w)^s
#check @Depth3.BlockPathLabel
#check @Depth3.card_blockPathLabel

-- Brick 10: compact recovery and the tight holographic switching count
#check @Depth3.freePosOf
#check @Depth3.posMaskOf
#check @Depth3.posMaskOf_freePosOf
#check @Depth3.compactMasks
#check @Depth3.blockPeelC
#check @Depth3.block_recovery_compact
#check @Depth3.blockMasks_eq_zipWith
#check @Depth3.block_injective_compact
#check @Depth3.block_switching_count_tight

-- Brick 11: count → probability bound (Håstad payoff, holographic dress)
#check @Depth3.block_switching_count_explicit
#check @Depth3.shell_ratio_nat
#check @Depth3.block_switching_prob_le

-- Brick 12: geometric-tail collapse → closed Håstad form
#check @Depth3.shell_ratio_nat_gen
#check @Depth3.term_ratio_q
#check @Depth3.geom_tail_le
#check @Depth3.sum_term_le
#check @Depth3.block_switching_prob_closed

-- Brick 13: circuit collapse (probabilistic method / union bound over the shell)
#check @Depth3.exists_avoiding_all
#check @Depth3.gateDeepSet
#check @Depth3.gateDeepSet_card_le
#check @Depth3.circuit_collapse_exists

-- Brick 14: DT → CNF/DNF representation swap (the ∨∧ ↦ ∧∨ depth-reduction step)
#check @Depth3.DTree
#check @Depth3.DTree.eval
#check @Depth3.DTree.depth
#check @Depth3.DTree.eval_eq_dnf
#check @Depth3.DTree.toDNF_width
#check @Depth3.DTree.eval_eq_cnf
#check @Depth3.DTree.toCNF_width
#check @Depth3.DTree.dnf_cnf_swap

-- Brick 15: one full depth-reduction step d → d-1 (associativity collapse)
#check @Depth3.DTree.bigAnd_eq_cnf
#check @Depth3.DTree.bigAndCNF_width
#check @Depth3.DTree.bigOr_eq_dnf
#check @Depth3.DTree.bigOrDNF_width
#check @Depth3.DTree.depth_reduction_step

-- Brick 16: concrete alternating circuit datatype + iterated same-type collapse
#check @Depth3.Circ
#check @Depth3.Circ.eval
#check @Depth3.Circ.height
#check @Depth3.Circ.eval_and_iff
#check @Depth3.Circ.eval_or_iff
#check @Depth3.Circ.bigAnd_flatten_eval
#check @Depth3.Circ.bigOr_flatten_eval
#check @Depth3.DTree.toCirc
#check @Depth3.DTree.toCirc_eval
#check @Depth3.DTree.toCirc_clause_width

-- Brick 17: one formal depth-reduction theorem d → d-1 over Circ
#check @Depth3.DTree.cnfToCirc
#check @Depth3.DTree.cnfToCirc_eval
#check @Depth3.Circ.height_cnfToCirc_le
#check @Depth3.DTree.and_trees_depth_reduction
#check @Depth3.DTree.and_trees_cnf_width
#check @Depth3.DTree.and_trees_height_le

-- Audit artifact: additive-sheet cross-block vanishing (the p-vs-np1 flaw, formalized)
#check @AdditiveSheetAudit.vars_pderiv_le
#check @AdditiveSheetAudit.additive_sheet_cross_block_vanish

end PallLean.Paper93.DeepMath.PathB

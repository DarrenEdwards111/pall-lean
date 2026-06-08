import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockTightCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCircuitCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeSwap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Circuit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitDepthReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Parity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ACZeroParity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitBudget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitRestrict
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ClauseTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfRestrict
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3QueryTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree
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

## Parity lower bound + AC⁰ endpoint (bricks 18–19, steps 5–6)

`shallow_dtree_not_parity` (step 6): a decision tree of depth `< n` cannot compute parity — proved via
full variable sensitivity (`parity_flip`) + off-path invariance (`eval_invariant_off_path`) +
`pathVars_card_le_depth`.  `circuit_not_parity_of_shallow` (the bridge): any circuit equal to a shallow
tree fails parity, making the pipeline an actual lower bound.  `and_of_shallow_dts_not_parity` is the
depth-3 endpoint (one switching round + bridge); `iterate_collapse` shows rounds compose by
transitivity.

## The quantitative budget (brick 20)

`circuit_collapse_budget` discharges the **per-round existence** from a clean closed-form inequality:
if `G · (2^w · 2K/(n-K+1))^s / (1 - 2K/(n-K+1)) < 1` (union bound over `G` gates, in closed Håstad
form) then one restriction in the `K`-star shell makes every gate's block-DT shallow (depth `< s`).  It
combines `circuit_collapse_exists` (union bound) with `sum_term_le` (closed Håstad tail), so the messy
cumulative shell sum never appears.

## The cross-round core (brick 21)

`parity_needs_full_depth_rel` is the invariant the multi-round argument carries forward: after fixing
some variables (a restriction `ρ`), parity *restricted to the survivors* still needs depth
`≥ #survivors`.  `circuit_not_parity_rel` is the relativized bridge (works mid-recursion, on
`ρ`-consistent inputs).  `reduce_chain` shows any number of switching rounds compose by eval-transitivity
(`EvalChain` + `evalChain_eval`), generalising `iterate_collapse`.

What is now machine-checked: the **entire structural pipeline**, the **per-round quantitative budget**
(`circuit_collapse_budget`), the **cross-round composition** (`reduce_chain`), and **both halves of the
final contradiction** (`parity_needs_full_depth_rel` survives restriction; `circuit_not_parity_rel`
applies it).  ## The restriction operation (brick 22)

`Circ.restrict ρ c` applies a restriction (a fixed literal becomes a constant gate); `eval_restrict`
proves its substitution semantics `eval x (restrict ρ c) = eval (override ρ x) c`, and
`eval_restrict_agree` that it agrees with `c` on `ρ`-consistent inputs.  `restricted_circuit_not_parity`
is the capstone: a switching round's output on the *restricted* circuit (`restrict ρ c ≡` shallow tree,
depth `< #survivors`) now feeds the relativized parity bridge automatically, with no manual
eval-equality hypothesis — the restriction-application piece is discharged.

## The model bridge atom (brick 23)

`termTree`/`clauseTree` compile a bottom term (`Rung4Literal` list / `Clause`) to a binary `DTree`,
proven to compute the conjunction (`termTree_eval`) with depth `≤` width (`termTree_depth`) — the
literal/term-level bridge between the `blockStream` switching world and the `DTree` parity world.

## Descent assembly, increment 1 + depth-2 parity bound (brick 24)

`dnfTree` glues the term-trees (via `termTreeCont` continuations) into a *single* `DTree` computing the
whole DNF (`dnfTree_eval`), with depth `≤ Σ widths` (`dnfTree_depth`), i.e. `≤ #clauses · w`
(`dnfTree_depth_le_mul`).  Composing with the parity lower bound gives a **genuine, unconditional,
complete** result:

`dnf_parity_size_bound` — **a width-`≤ w` DNF computing parity needs `≥ n/w` terms** (`n ≤ #clauses · w`).

This is the base case of the AC⁰ hierarchy (depth 2), fully proved.

## Descent assembly, increment 2 — restriction pruning (brick 25)

`restrictDnf` prunes the DNF under a restriction: dead clauses (a literal forced false) drop, live
clauses keep only free literals.  `restrictDnfTree_eval` proves the pruned tree computes the DNF on the
subcube (`ρ`-consistent inputs), and `restrictDnfTree_depth_le` bounds its depth by `#live · w` — strictly
smaller whenever the restriction kills clauses.  Built in the clean `Rung4Literal`/`DTree` world (no
block-arc dependency), no `sorry`.

## Descent assembly, increment 3 (the adaptive canonical tree) — step 1 (brick 26)

`queryAll` is the per-block query mechanism: a complete binary subtree querying the active term's free
variables, threading each leaf's assignment into a continuation.  `queryAll_eval` (runs the continuation
on the leaf assignment `x` selects) and `queryAll_depth` (depth `≤ #vars + d`) are the two properties
the adaptive tree needs per block.

Step 2 (brick 27): `canonicalDTree cs w F σ` — the adaptive tree, fuel-based, mirroring `blockStream`:
satisfying branch → `true`, no active term → `false`, otherwise `queryAll` the active term's free
variables and recurse on each falsifying leaf with that leaf's **own extended restriction** (`extendσ`,
the per-leaf threading).  `canonicalDTree_depth_le` proves the fuel depth bound `≤ F · w`.

Remaining steps of increment 3 (built incrementally): eval-correctness against the DNF (via the
`killTerm`/`activeTerm` dichotomy); the tighter `≤ blockStream.length · w` bound (descent-length
monotonicity under restriction extension); then the parity-bridge connection (once `< s·w`).  The
genuinely hard switching-lemma core, built honestly in small bricks; no `sorry`.  AC⁰ ceiling; not
P≠NP-strength.

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

-- Brick 18: the parity lower bound (contradiction target — step 6)
#check @Depth3.DTree.parity
#check @Depth3.DTree.parity_flip
#check @Depth3.DTree.pathVars_card_le_depth
#check @Depth3.DTree.eval_invariant_off_path
#check @Depth3.DTree.parity_needs_full_depth
#check @Depth3.DTree.shallow_dtree_not_parity

-- Brick 19: the AC⁰ pipeline endpoint — circuits vs parity (the lower-bound bridge)
#check @Depth3.circuit_not_parity_of_shallow
#check @Depth3.and_of_shallow_dts_not_parity
#check @Depth3.iterate_collapse

-- Brick 20: the quantitative restriction budget (closed Håstad form, per-round existence)
#check @Depth3.circuit_collapse_budget

-- Brick 21: the relativized parity lower bound + multi-round chain (cross-round core)
#check @Depth3.DTree.agreeRestriction
#check @Depth3.DTree.parity_needs_full_depth_rel
#check @Depth3.DTree.circuit_not_parity_rel
#check @Depth3.EvalChain
#check @Depth3.evalChain_eval
#check @Depth3.reduce_chain

-- Brick 22: the restriction-application operation on circuits (threads rounds)
#check @Depth3.Circ.restrict
#check @Depth3.Circ.override
#check @Depth3.Circ.eval_restrict
#check @Depth3.Circ.eval_restrict_agree
#check @Depth3.restricted_circuit_not_parity

-- Brick 23: the term/clause → DTree bridge atom (blockStream world ↔ DTree world)
#check @Depth3.DTree.termTree
#check @Depth3.DTree.termTree_eval
#check @Depth3.DTree.termTree_depth
#check @Depth3.DTree.clauseTree
#check @Depth3.DTree.clauseTree_eval
#check @Depth3.DTree.clauseTree_depth

-- Brick 24: DNF → DTree (descent assembly, increment 1) + the depth-2 parity lower bound
#check @Depth3.DTree.termTreeCont
#check @Depth3.DTree.termTreeCont_eval
#check @Depth3.DTree.termTreeCont_depth
#check @Depth3.DTree.dnfTree
#check @Depth3.DTree.dnfValue
#check @Depth3.DTree.dnfTree_eval
#check @Depth3.DTree.dnfTree_depth
#check @Depth3.DTree.dnfTree_depth_le_mul
#check @Depth3.DTree.dnf_parity_size_bound

-- Brick 25: DNF → DTree (descent assembly, increment 2 — restriction pruning)
#check @Depth3.DTree.litKilled
#check @Depth3.DTree.clauseLive
#check @Depth3.DTree.restrictDnf
#check @Depth3.DTree.restrictDnf_dnfValue
#check @Depth3.DTree.restrictDnfTree_eval
#check @Depth3.DTree.restrictDnfTree_depth_le

-- Brick 26: per-block query subtree (descent assembly, increment 3, step 1)
#check @Depth3.DTree.queryAll
#check @Depth3.DTree.queryAll_eval
#check @Depth3.DTree.queryAll_depth

-- Brick 27: the adaptive canonical decision tree (descent assembly, increment 3, step 2)
#check @Depth3.canonicalDTree
#check @Depth3.freeVarsOf
#check @Depth3.extendσ
#check @Depth3.canonicalDTree_depth_le

-- Audit artifact: additive-sheet cross-block vanishing (the p-vs-np1 flaw, formalized)
#check @AdditiveSheetAudit.vars_pderiv_le
#check @AdditiveSheetAudit.additive_sheet_cross_block_vanish

end PallLean.Paper93.DeepMath.PathB

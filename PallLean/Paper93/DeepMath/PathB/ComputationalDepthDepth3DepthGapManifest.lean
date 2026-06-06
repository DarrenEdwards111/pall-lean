import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonLabelDepthGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NoSkipReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureFalsifyReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EmptySkipWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthBadViaEncLits
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalDTComputesDNF
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FalsifiedMonotone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ReplayPathLenBad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestPathLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AlignReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CleanSkipReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ConfoundFence
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverRhoObligation

/-!
# The `canonLabelLen ↔ max-depth` gap, fenced from both sides

A machine-checked index of the depth/decoder arc.  Every `#check` is a proved theorem (clean axioms,
no `sorry`, no `native_decide`).  The collapse needs a depth-`≤budget` decision **tree** for `D|ρ`,
i.e. the **max-branch** `canonicalDT.depth`.  Two switching routes approach it, controlling *different*
quantities — and the gap between them is fenced here from both sides.

## The object: the canonical tree computes `D`, depth is a concrete branch length

* `canonicalDT_computes_dnf` / `canonicalDT_collapse_of_depth_le` — the canonical tree over the
  clause-encoding of `D` computes `D` on the subcube; a depth-`≤budget` tree collapses it.
* `deepestPath_length_eq_depth` — `depth = (deepestPath …).length` (depth is a concrete branch).
* `deepestPathLabel_length_eq_depth` / `deepestPathLabel_idx_lt` / `depthBad_eq_labelLenBad` — the full
  deepest branch packs into a `(2w)^depth` label; `{depth = s}` is its label-length set.
* `canonicalDT_depth_le_stars` (upper) and `canonicalDT_depth_ge_replay` (lower, the all-falsify
  branch) bracket the depth.

## Side A — the encLits / satisfying-completion route (COMPLETE, controls `canonLabelLen`)

The satisfying completion `σ*` makes "first satisfied term" identify the active clause, so this route
is complete — but it controls `canonLabelLen`, the **single satisfying-completion path** length.

* `canonMarkLabel_switching_count` — the full tight `|Bad| ≤ |Short|·(2w)^s` count.
* `canon_count_pathLenBad` / `pathLenBadGt_card_le` — bounds `{ρ : canonLabelLen > budget}`.
* `exists_good_canonLabelLen` — extracts a restriction with `canonLabelLen ρ cs ≤ budget`.

## Side B — the deepest-branch route (controls the true max-depth; reconstruction closed in 3 regimes)

This route bounds the max-depth directly via `ReconstructionCorrect` (recover `deepestSel` from
`(deepestEnd, label)`), assembled from proven per-step mechanisms:

* value recovery — `litTrue_deepestEnd_of_satisfy_step`, `litFalse_deepestEnd_active_eq`;
* clause-order monotonicity — `activeTerm_advance_stable`, `activeTerm_falsify_advances`,
  `termFalsified_deepestEnd_stable`, `prefix_falsified_through_branch`;
* reverse-peel + injectivity — `freeOn_deepestEnd`, `deepestEnd_inj`;
* the reduction — `reconstruction_of_satSel_decoder`, `deepest_switching_count_of_reconstruction`;
* depth-based G1-core — `replay_count_pathLenBad`, `replay_pathLenBad_le_depthBad`.

`ReconstructionCorrect` is discharged in **five regimes**, isolating the irreducible core to a single
combinatorial confound:
* pure-satisfy (`pure_satisfy_switching_count_depth`, elsewhere),
* pure-falsify (`reconstruction_pure_falsify`, `deepest_pure_falsify_count`),
* interleaved no-skip (`reconstruction_no_skip`, `deepest_no_skip_reconstruction_count`),
* **align** (`reconstruction_align`) — replaces no-skip's all-blocks-non-empty `hns` by the *exact*
  alignment condition it buys (`halign`); `reconstruction_no_skip_via_align` recovers no-skip,
* **clean-skip** (`reconstruction_clean_skip`) — allows **interior** empty blocks when each is exactly
  a falsified leaf clause (`hskip`), reinserting them from the end-state (`reinsert` /
  `reinsert_map_filter`).

## The gap, fenced from BOTH sides + the confound machine-checked (the irreducible Håstad core)

The two routes control different quantities; bridging them is the open switching content.  It is
fenced here so it cannot be mistaken for a missing lemma:

* **Fence 1 — pointwise no-go.**  `encLits_length_lt_depth` / `depth_gt_satpath_witness`:
  `depth ≤ canonLabelLen` is **provably false** (a verified witness `[{x₀},{¬x₀,x₁}]`).  So the gap
  does **not** reduce to any pointwise `canonLabelLen` bound; it can only close in the aggregate.
* **Fence 2 — empty-skip wall (information loss).**  `tight_pack_skip_invariant` /
  `tight_decode_replayLabel` / `ungroupBlocks_filter_invariant` / `groupBlocks_ungroupBlocks_filter`:
  the tight `(2w)^s` packing is invariant under deleting empty (skip) blocks — it cannot record the
  clause-alignment the decoder's positional `zip` needs.
* **Fence 3 — the confound is real and uncovered** (`clB_confound` / `confound_uncovered`, machine-
  checked by `decide` on `[{x₀},{x₁,x₂}]`).  Outside no-skip ∪ clean-skip ∪ align lies exactly the
  *confound*: a clause **falsified at the leaf that also received satisfy steps** (a non-empty block
  on a falsified clause), indistinguishable at the end-state from a clean skip.

The residual is therefore precisely the confound, and decoding it needs *attributing* a falsified
clause's satisfy positions to it — recovered only by a **forward-replay / clause-order reconstruction
of `ρ`** (Razborov's decoder), i.e. Håstad's switching lemma itself.  Everything around it — object,
both routes, **five** reconstruction regimes, good-restriction extraction, and the confound fenced as
non-empty — is proved.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- The object: canonical tree computes D, depth is a concrete branch length.
#check @Depth3.canonicalDT_computes_dnf
#check @Depth3.canonicalDT_collapse_of_depth_le
#check @Depth3.deepestPath_length_eq_depth
#check @Depth3.deepestPathLabel_length_eq_depth
#check @Depth3.deepestPathLabel_idx_lt
#check @Depth3.depthBad_eq_labelLenBad
#check @Depth3.canonicalDT_depth_le_stars
#check @Depth3.canonicalDT_depth_ge_replay

-- Side A: the encLits / satisfying-completion route (complete; controls canonLabelLen).
#check @SwitchingCounting.canonMarkLabel_switching_count
#check @SwitchingCounting.canon_count_pathLenBad
#check @SwitchingCounting.pathLenBadGt_card_le
#check @SwitchingCounting.exists_good_canonLabelLen

-- Side B: the deepest-branch route (true max-depth; reconstruction mechanisms + reduction).
#check @Depth3.litTrue_deepestEnd_of_satisfy_step
#check @Depth3.litFalse_deepestEnd_active_eq
#check @Depth3.activeTerm_advance_stable
#check @Depth3.activeTerm_falsify_advances
#check @Depth3.termFalsified_deepestEnd_stable
#check @Depth3.prefix_falsified_through_branch
#check @Depth3.freeOn_deepestEnd
#check @Depth3.deepestEnd_inj
#check @Depth3.reconstruction_of_satSel_decoder
#check @Depth3.deepest_switching_count_of_reconstruction
#check @SwitchingCounting.replay_count_pathLenBad
#check @SwitchingCounting.replay_pathLenBad_le_depthBad

-- Side B: ReconstructionCorrect discharged in five regimes (pure-satisfy elsewhere).
#check @Depth3.reconstruction_pure_falsify
#check @Depth3.deepest_pure_falsify_count
#check @Depth3.reconstruction_no_skip
#check @Depth3.deepest_no_skip_reconstruction_count
#check @Depth3.reconstruction_align
#check @Depth3.reconstruction_no_skip_via_align
#check @Depth3.reconstruction_clean_skip
#check @Depth3.reinsert_map_filter

-- Fence 1: the pointwise no-go (depth ≤ canonLabelLen is false).
#check @Depth3.encLits_length_lt_depth
#check @Depth3.depth_gt_satpath_witness

-- Fence 2: the empty-skip wall (the tight packing loses the skip-alignment).
#check @SwitchingCounting.ungroupBlocks_filter_invariant
#check @SwitchingCounting.groupBlocks_ungroupBlocks_filter
#check @Depth3.tight_decode_replayLabel
#check @Depth3.tight_pack_skip_invariant

-- Fence 3: the confound is real and uncovered (machine-checked on [{x₀},{x₁,x₂}]).
#check @Depth3.clB_confound
#check @Depth3.confound_uncovered

-- The open core, as a named target: the Håstad/Razborov forward-replay reconstruction.
-- `RecoverRhoObligation` is stated, not proved; it is *equivalent* to `ReconstructionCorrect`
-- (via the proved `freeOn_deepestEnd`), so the clause-order `recoverRho` and the satisfy-step
-- decoder are the same switching-lemma problem — no shortcut.
#check @Depth3.RecoverRhoObligation
#check @Depth3.recoverRhoObligation_iff_reconstructionCorrect

end PallLean.Paper93.DeepMath.PathB

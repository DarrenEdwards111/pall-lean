import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ReconstructionFalsify
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ForwardScanPath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LiteralBijection
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FalsifyDeepestCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseFactor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFalsifyPart
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPositionLit

/-!
# Kernel handoff: the one open target, its scaffolding, and the exact obligation

This file is a **self-contained target specification** for the single open kernel of the depth-3
switching arc.  Everything around it is proved (all `#check`s below typecheck, clean axioms); the
kernel itself is Håstad's switching-lemma decoding for satisfy-containing branches.

## THE TARGET

Prove, for the **depth-bad set** `Bad := {ρ : (canonicalDT cs (stars ρ) ρ).depth > budget}`
(equivalently `{ρ : deepestPath cs (stars ρ) ρ |>.length > budget}`, via
`Depth3.deepestPath_length_eq_depth`):

    Depth3.ReconstructionCorrect cs w s F Bad

i.e. exhibit a `(2w)^s` label `lab : Restriction n → PathLabel w s` and a decoder
`D : Restriction n → PathLabel w s → Finset (Fin n)` with
`∀ ρ ∈ Bad, D (deepestEnd cs F ρ) (lab ρ) = deepestSel cs F ρ`.

Then `Depth3.deepest_switching_count_of_reconstruction` gives `|Bad| ≤ |Short|·(2w)^s` (the tight
`depth ≤ s`), which closes `depth3_master_squeeze` unconditionally.

## WHAT IS ALREADY PROVED (reuse these)

* `Depth3.freeOn_deepestEnd` / `Depth3.deepestEnd_inj` — recovery loop + injectivity: `ρ` is
  determined by `(deepestEnd, deepestSel)`.  So the decoder only needs to recover `deepestSel`.
* `Depth3.decodedSel_subset_deepestSel` — **the falsify-part is label-free**: under "ρ falsifies
  nothing", `decodedSel (deepestEnd) ⊆ deepestSel`.  So the decoder needs only `deepestSel \
  decodedSel` from the label.
* `Depth3.reconstruction_of_labelfree` — if `deepestSel` is recoverable from the end-state alone,
  `ReconstructionCorrect` holds (constant label).
* `Depth3.reconstruction_of_deepest_eq_replay` — closed for the **falsify-deepest** regime
  (deepest branch = falsify path), via `SwitchingCounting.decodedSel_eq_replaySel`.
* `Depth3.termFalsified_deepestEnd` / `Depth3.termFalsified_fixVar_of_free` — forward-scan
  monotonicity: the falsified frontier persists to the end-state.
* `Depth3.freeOn_fixVar_free` — per-step recovery for any bit (the recovery loop for general branches).
* `SearchDischarge.rlitToTlit` + `SearchDischarge.tautDNF_to_dtRef_tautAx` — the literal bijection and
  the concrete circuit ⟹ refuting-`DTRef` kernel (in `(· ∈ Ax)` form).

## THE EXACT REMAINING OBLIGATION

Recover `deepestSel \ decodedSel` — the **satisfy-step variables** (queried with a `true`-bit, which
carry *no* false literal at the end-state) — from the end-state plus the `(2w)^s` label.  This is the
forward-scan reconstruction for satisfy-containing branches: scan clauses in cs-order; the first live
clause in the restriction reconstructed so far is the active clause at that step (the monotonicity
backbone is proved); free its labelled path-variables; recurse.  The position-in-clause part is
`SwitchingCounting.clauseLitAt`; the open content is the active-clause identification under
satisfy-steps.

This is the famous hard core of Håstad's switching lemma.  Ceiling: AC⁰/depth-3.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- The target and the lemma that it suffices:
#check @Depth3.ReconstructionCorrect
#check @Depth3.deepest_switching_count_of_reconstruction

-- The proved scaffolding the kernel proof should reuse:
#check @Depth3.freeOn_deepestEnd
#check @Depth3.deepestEnd_inj
#check @Depth3.decodedSel_subset_deepestSel
#check @Depth3.reconstruction_of_labelfree
#check @Depth3.reconstruction_of_deepest_eq_replay
#check @Depth3.termFalsified_deepestEnd
#check @Depth3.termFalsified_fixVar_of_free
#check @Depth3.freeOn_fixVar_free
#check @Depth3.deepestPath_length_eq_depth
#check @SwitchingCounting.decodedSel_eq_replaySel
#check @SwitchingCounting.clauseLitAt
#check @SearchDischarge.rlitToTlit
#check @SearchDischarge.tautDNF_to_dtRef_tautAx

-- The downstream consumers (already proved) that the closed kernel feeds:
#check @collapseModel_of_dtRefKernel
#check @circuit_lower_bound_of_kernel

end PallLean.Paper93.DeepMath.PathB

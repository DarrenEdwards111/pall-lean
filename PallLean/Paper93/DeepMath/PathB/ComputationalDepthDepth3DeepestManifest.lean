import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockWellFormed
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestLeafClause
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestActiveId
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ActiveMonotone

/-!
# Deepest-branch switching arc: manifest

A machine-checked index of the deepest-branch reconstruction arc — the `(2w)^s` switching count for
the canonical decision tree's *depth* (`{ρ : canonicalDT.depth ≥ s}`).  Every `#check` below refers to
a proved theorem (clean axioms, no `sorry`); together they verify the arc composes as claimed.

## The reduction target

`ReconstructionCorrect cs w s F Bad` ⟹ the tight `|Bad| ≤ |Short|·(2w)^s`
(`deepest_switching_count_of_reconstruction`).  `ReconstructionCorrect` asks for a `(2w)^s` label and
a decoder recovering the deepest branch's selected variables from the leaf.

## Pure-satisfy regime — FULLY CLOSED

When the deepest branch has no falsify step (clean active clause, fuel-limited leaf), the active clause
is constant and the recovery is end-to-end:
* `activeTerm_deepestEnd_pure_satisfy`, `deepestSatSel_eq_decode_pure_satisfy`,
  `reconstructionCorrect_pure_satisfy`, `pure_satisfy_switching_count_depth`
  (the tight `(2w)^s` bound, with the size condition `canonicalDT.depth = s`).

## General interleaved case — reduced to one construction

The full decoder is factored and discharged down to a single remaining construction:

1. **Threading** — `deepestSel = decodedSel(end) ∪ deepestSatSel` (falsify part label-free):
   `decodedSel_union_satSel_eq_deepestSel`, `reconstruction_of_satSel_decoder`.
2. **Decode** (unconditional) — `deepestSatSel = decodeSatSeq (deepestSatSeq)`:
   `deepestSatSel_eq_decodeSatSeq`.
3. **Transition layer** — `deepestEnd cs (F+1) σ = deepestEnd cs F (deepestStep cs F σ)`:
   `deepestEnd_succ`; forward leaf-identification `activeTerm_deepestEnd_of_not_falsified`.
4. **Clause side (end-state-readable, ordered)** — `deepest_falsified_clause_active`,
   `deepestSel_mem_leaf_clause`, `deepestSatSeq_clause_leaf`, `deepestSatSeq_clause_mem_leafClauses`,
   `activeTerm_fixVar_no_backtrack` (non-backtracking).
5. **Grouping + reductions** — `clauseGrouping_flatten` (free round-trip via `List.splitBy`),
   `reconstruction_of_canonGroupDecoder`, `clauseGrouping_ne_nil`,
   `clauseGrouping_block_entry_mem_leafClauses`.

So `ReconstructionCorrect` (general) follows from one construction `Dgrp`: recover
`clauseGrouping (deepestSatSeq cs F ρ)` from `(deepestEnd, label)` — i.e. assign the label's
position-runs to the (ordered, end-state-readable `leafClauses`) clauses.  **The lone remaining gap**
is that run-matching, whose obstruction is the empty-block skip (immediately-falsified clauses are
leaf-readable but contribute no step), requiring the full Håstad label-driven replay.  Everything
around it is proved here.  Ceiling: AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- The reduction target and the count it yields.
#check @Depth3.ReconstructionCorrect
#check @Depth3.deepest_switching_count_of_reconstruction

-- Pure-satisfy regime: fully closed, end-to-end, tight (2w)^s depth count.
#check @Depth3.activeTerm_deepestEnd_pure_satisfy
#check @Depth3.deepestSatSel_eq_decode_pure_satisfy
#check @Depth3.reconstructionCorrect_pure_satisfy
#check @Depth3.pure_satisfy_switching_count_depth

-- General interleaved: threading (falsify part label-free).
#check @Depth3.decodedSel_union_satSel_eq_deepestSel
#check @Depth3.reconstruction_of_satSel_decoder

-- General interleaved: unconditional per-step-clause decode.
#check @Depth3.deepestSatSel_eq_decodeSatSeq

-- General interleaved: transition layer + forward leaf-identification.
#check @Depth3.deepestEnd_succ
#check @Depth3.activeTerm_deepestEnd_of_not_falsified
#check @Depth3.activeTerm_fixVar_no_backtrack

-- General interleaved: clause side (end-state-readable, ordered).
#check @Depth3.deepest_falsified_clause_active
#check @Depth3.deepestSel_mem_leaf_clause
#check @Depth3.deepestSatSeq_clause_leaf
#check @Depth3.deepestSatSeq_clause_mem_leafClauses

-- General interleaved: grouping + the reduction to the lone remaining construction `Dgrp`.
#check @Depth3.clauseGrouping_flatten
#check @Depth3.reconstruction_of_canonGroupDecoder
#check @Depth3.clauseGrouping_ne_nil
#check @Depth3.clauseGrouping_block_entry_mem_leafClauses

end PallLean.Paper93.DeepMath.PathB

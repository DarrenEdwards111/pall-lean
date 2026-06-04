import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockDecoder
import Mathlib.Data.List.SplitBy

/-!
# Canonical clause-grouping: the block decoder's target, with a free round-trip

`List.splitBy` groups a list into runs, and `List.flatten_splitBy` flattens them back to the original
— unconditionally.  Grouping `deepestSatSeq` by clause therefore round-trips for free, so the block
decoder's target reduces to producing this canonical grouping.

* `clauseGrouping` — group `deepestSatSeq` into per-clause runs via `List.splitBy` on clause equality.
* `clauseGrouping_flatten` — the grouping flattens back to the original (`List.flatten_splitBy`).
* `reconstruction_of_groupedDecoder` — `ReconstructionCorrect` from a decoder whose grouped output
  flattens to `deepestSatSeq`.
* `reconstruction_of_canonGroupDecoder` — **the precise target**: `ReconstructionCorrect` from a
  decoder producing exactly `clauseGrouping (deepestSatSeq …)`.

So the entire general interleaved `ReconstructionCorrect` reduces to one concrete construction:
recover the canonical clause-grouping of `deepestSatSeq` from the end-state and label.  The clauses
are end-state-readable (`deepestSatSeq_clause_leaf`) and ordered (non-backtracking); the remaining work
is assigning the label's position-runs to them.  Not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Group a `(clause, position)` list into per-clause runs (consecutive entries with equal clause). -/
def clauseGrouping (l : List (Clause n × ℕ)) : List (List (Clause n × ℕ)) :=
  l.splitBy (fun a b => decide (a.1.lits = b.1.lits))

/-- The clause-grouping flattens back to the original list (free, via `List.flatten_splitBy`). -/
theorem clauseGrouping_flatten (l : List (Clause n × ℕ)) : (clauseGrouping l).flatten = l :=
  List.flatten_splitBy _ l

/-- **Reduction to a grouped decoder.**  `ReconstructionCorrect` follows from any decoder whose grouped
output flattens to `deepestSatSeq`. -/
theorem reconstruction_of_groupedDecoder {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (Dgrp : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s →
      List (List (Clause n × ℕ)))
    (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (hgrp : ∀ ρ ∈ Bad, (Dgrp (deepestEnd cs F ρ) (lab ρ)).flatten = deepestSatSeq cs F ρ) :
    ReconstructionCorrect cs w s F Bad :=
  reconstruction_of_satSeq_decoder hnf (fun π l => (Dgrp π l).flatten) lab hgrp

/-- **The precise block-delimiting target.**  `ReconstructionCorrect` follows from a decoder producing
exactly the canonical clause-grouping of `deepestSatSeq` — the round-trip is then `flatten_splitBy`. -/
theorem reconstruction_of_canonGroupDecoder {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (Dgrp : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s →
      List (List (Clause n × ℕ)))
    (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (hcg : ∀ ρ ∈ Bad, Dgrp (deepestEnd cs F ρ) (lab ρ) = clauseGrouping (deepestSatSeq cs F ρ)) :
    ReconstructionCorrect cs w s F Bad :=
  reconstruction_of_groupedDecoder hnf Dgrp lab
    (fun ρ hρ => by rw [hcg ρ hρ]; exact clauseGrouping_flatten _)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.clauseGrouping_flatten
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_of_canonGroupDecoder
